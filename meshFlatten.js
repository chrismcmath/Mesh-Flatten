 /**
 * MeshFlatten v0.1
 * Three.js Mesh Flattener

	Chris McMath
	http://chrismcmath.com

	Using Gautama Dude's JS translation of Paul Bourke's intersection algorithm.

 * http://github.com/chrismcmath/meshFlatten
 */

var MESHFLATTEN = MESHFLATTEN || {};

MESHFLATTEN.Flatten = function(flatGeom)
{
	var scope = this;
	this.faceRoot = null;
	this.mesh = flatGeom;
	this.alteredVertices = [];
	this.unflattenedVertices = new Array(flatGeom.vertices.length);
	this.flattenedVertices = new Array(flatGeom.vertices.length);

	this.rebuildNode = function(node, faces, vertices)
	{
		var v1data = node.geomData[0];
		var v2data = node.geomData[1];
		var v3data = node.geomData[2];
		var v1 = vertices[v1data.vertex];
		var v2 = vertices[v2data.vertex];

		var intersectData = scope.intersection(v1.x,v1.y,v1data.distance,v2.x,v2.y,v2data.distance);

		while(!intersectData)
		{
			v1data.distance *= 1.1;
			v2data.distance *= 1.1;
			intersectData = scope.intersection(v1.x,v1.y,v1data.distance,v2.x,v2.y,v2data.distance);
		}

		if(isNaN(intersectData[0]))
			return;

		/* ---- Get vector to previous face center ----*/
		var opFace = faces[v3data.oppositeFace];
		var parentFacePosition = [(vertices[opFace.a].x + vertices[opFace.b].x + vertices[opFace.c].x)/3,
								(vertices[opFace.a].y + vertices[opFace.b].y + vertices[opFace.c].y)/3,
								(vertices[opFace.a].z + vertices[opFace.b].z + vertices[opFace.c].z)/3];

		var ThirdA = [intersectData[0], intersectData[2], 0];
		var ThirdB = [intersectData[1], intersectData[3], 0];
		var midPoint = [(v1.x + v2.x)/2, (v1.y + v2.y)/2, 0];

		var midToA = scope.subtract(ThirdA,midPoint);
		var midToB = scope.subtract(ThirdB,midPoint);
		var midToFaceMiddle = scope.subtract(parentFacePosition,midPoint);

		var v3Position = {x: 0, y: 0};

		if(scope.dot(midToFaceMiddle,midToA) < scope.dot(midToFaceMiddle,midToB))
		{
			v3Position.x = intersectData[0];
			v3Position.y = intersectData[2];
			scope.flattenedVertices[v3data.vertex].z = 0;
		}
		else
		{
			v3Position.x = intersectData[1];
			v3Position.y = intersectData[3];
		}	

		//Only unfold a vertex which has yet to be unfolded, else stretch
		if(scope.alteredVertices.indexOf(v3data.vertex) == -1)
		{
			scope.flattenedVertices[v3data.vertex].x = v3Position.x;
			scope.flattenedVertices[v3data.vertex].y = v3Position.y;
			scope.flattenedVertices[v3data.vertex].z = 0;

			scope.alteredVertices.push(v3data.vertex);
		}
		else
		{
			scope.flattenedVertices[v3data.vertex].x = (v3Position.x + vertices[v3data.vertex].x)/2;
			scope.flattenedVertices[v3data.vertex].y = (v3Position.y + vertices[v3data.vertex].y)/2;
			scope.flattenedVertices[v3data.vertex].z = 0;
		}

		for(var i = 0; i < node.leaves.length; i++)
		{
			scope.rebuildNode(node.leaves[i],faces,vertices);
		}
	};

	/*------------- Unfold stuff --------------*/
	this.createTreeNode = function(flatGeom)
	{
		/*--- find decent startpoint -----*/
		var startIndex = 0;
		var goodPointFound = false;
		var currentMin;
		for(var i = 0; i < flatGeom.faces.length; i++)
		{
			var min = Math.abs(flatGeom.vertices[flatGeom.faces[i].a].z-flatGeom.vertices[flatGeom.faces[i].c].z)
						+ Math.abs(flatGeom.vertices[flatGeom.faces[i].b].z-flatGeom.vertices[flatGeom.faces[i].c].z)
						+ Math.abs(flatGeom.vertices[flatGeom.faces[i].a].z-flatGeom.vertices[flatGeom.faces[i].b].z);

			if(flatGeom.vertices[flatGeom.faces[i].a].z == flatGeom.vertices[flatGeom.faces[i].b].z
				&& flatGeom.vertices[flatGeom.faces[i].a].z == flatGeom.vertices[flatGeom.faces[i].c].z)
			{
				startIndex = i;
				goodPointFound = true;
				break;
			} 
			else if (min < currentMin || i == 0)
			{
				startIndex = i;
				currentMin = min;
			}
		}

		//Face root is a special case- must be handled as such
		scope.faceRoot = {index: startIndex, leaves: []};
		var remainingFaces = flatGeom.faces.slice(0);
		remainingFaces.splice(remainingFaces.indexOf(flatGeom.faces[scope.faceRoot.index]), 1);

		var leaves = scope.getConnectedFaces(flatGeom.faces[scope.faceRoot.index], remainingFaces, flatGeom.faces);

		//Remove children from the remaining faces
		for(var i = 0; i < leaves.length; i++)
		{
			remainingFaces.splice(remainingFaces.indexOf(flatGeom.faces[leaves[i]]),1);
		}
		//Add reference of child to the parent and dque
		var newQueue = new Array();
		for(var i = 0; i < leaves.length; i++)
		{
			var child = {index: leaves[i], leaves: [], parent: scope.faceRoot.index};
			scope.faceRoot.leaves.push(child);
			newQueue.unshift(child);
		}

		var _finished = false;

		while(!_finished)
		{
			var oldQueue = newQueue.slice(0);
			newQueue.length = 0;
			while(oldQueue.length > 0)
			{
				var node = oldQueue.pop();

				/*---- Work out length of 'third' node ----- */
				var thirdVertex = getThirdVertex(flatGeom.faces[node.index], flatGeom.faces[node.parent]);
				if(thirdVertex == flatGeom.faces[node.index].a)
				{
					var v1 = flatGeom.faces[node.index].b;
					var v2 = flatGeom.faces[node.index].c;
				}
				else if(thirdVertex == flatGeom.faces[node.index].b)
				{
					var v1 = flatGeom.faces[node.index].a;
					var v2 = flatGeom.faces[node.index].c;
				}
				else if(thirdVertex == flatGeom.faces[node.index].c)
				{
					var v1 = flatGeom.faces[node.index].a;
					var v2 = flatGeom.faces[node.index].b;
				}

				var x,y,z;
				dx = flatGeom.vertices[thirdVertex].x - flatGeom.vertices[v1].x;
				dy = flatGeom.vertices[thirdVertex].y - flatGeom.vertices[v1].y;
				dz = flatGeom.vertices[thirdVertex].z - flatGeom.vertices[v1].z;

				var v1Distance = Math.sqrt(dx*dx + dy*dy + dz*dz);

				dx = flatGeom.vertices[thirdVertex].x - flatGeom.vertices[v2].x;
				dy = flatGeom.vertices[thirdVertex].y - flatGeom.vertices[v2].y;
				dz = flatGeom.vertices[thirdVertex].z - flatGeom.vertices[v2].z;

				var v2Distance = Math.sqrt(dx*dx + dy*dy + dz*dz);

				// if(v1Distance == Infinity)
					// debugger;

				var geomData = [{vertex: v1, distance: v1Distance},{vertex: v2, distance: v2Distance},{vertex: thirdVertex, oppositeFace: node.parent}];
				node.geomData = geomData;

				var leaves = scope.getConnectedFaces(flatGeom.faces[node.index], remainingFaces, flatGeom.faces);

				//Remove children from the remaining faces
				for(var i = 0; i < leaves.length; i++)
				{
					remainingFaces.splice(remainingFaces.indexOf(flatGeom.faces[leaves[i]]),1);
				}

				for(var i = 0; i < leaves.length; i++)
				{
					var child = {index: leaves[i], leaves: [], parent: node.index};
					node.leaves.push(child);
					newQueue.unshift(child);
				}
			}
			if(newQueue.length == 0)
				_finished = true;
		}

		return scope.faceRoot;
	};

	this.unfold = function (fraction)
	{
		for(var i = 0; i < scope.unflattenedVertices.length; i++)
		{
			scope.mesh.vertices[i].x = scope.unflattenedVertices[i].x + (scope.flattenedVertices[i].x - scope.unflattenedVertices[i].x)*fraction;
			scope.mesh.vertices[i].y = scope.unflattenedVertices[i].y + (scope.flattenedVertices[i].y - scope.unflattenedVertices[i].y)*fraction;
			scope.mesh.vertices[i].z = scope.unflattenedVertices[i].z + (scope.flattenedVertices[i].z - scope.unflattenedVertices[i].z)*fraction;
		}
		scope.mesh.verticesNeedUpdate = true;
	};

	/*-------- Utility classes --------*/
	this.intersection = function(x0, y0, r0, x1, y1, r1) {
	    var a, dx, dy, d, h, rx, ry;
	    var x2, y2;

	    /* dx and dy are the vertical and horizontal distances between
	     * the circle centers.
	     */
	    dx = x1 - x0;
	    dy = y1 - y0;

	    /* Determine the straight-line distance between the centers. */
	    d = Math.sqrt((dy*dy) + (dx*dx));

	    /* Check for solvability. */
	    if (d > (r0 + r1)) {
	        /* no solution. circles do not intersect. */
	        return false;
	    }
	    if (d < Math.abs(r0 - r1)) {
	        /* no solution. one circle is contained in the other */
	        return false;
	    }

	    /* 'point 2' is the point where the line through the circle
	     * intersection points crosses the line between the circle
	     * centers.  
	     */

	    /* Determine the distance from point 0 to point 2. */
	    a = ((r0*r0) - (r1*r1) + (d*d)) / (2.0 * d) ;

	    /* Determine the coordinates of point 2. */
	    x2 = x0 + (dx * a/d);
	    y2 = y0 + (dy * a/d);

	    /* Determine the distance from point 2 to either of the
	     * intersection points.
	     */
	    h = Math.sqrt((r0*r0) - (a*a));

	    /* Now determine the offsets of the intersection points from
	     * point 2.
	     */
	    rx = -dy * (h/d);
	    ry = dx * (h/d);

	    /* Determine the absolute intersection points. */
	    var xi = x2 + rx;
	    var xi_prime = x2 - rx;
	    var yi = y2 + ry;
	    var yi_prime = y2 - ry;

	    return [xi, xi_prime, yi, yi_prime];
	};
	this.getNoVerticesInCommon = function(f1, f2)
	{
		var vic = 0;

		if(f1.a == f2.a || f1.a == f2.b || f1.a == f2.c)
			vic++;
		if(f1.b == f2.a || f1.b == f2.b || f1.b == f2.c)
			vic++;
		if(f1.c == f2.a || f1.c == f2.b || f1.c == f2.c)
			vic++;

		return vic;
	};
	this.getConnectedFaces = function(parent, remainingFaces, allFaces)
	{
		var children = [];
		for(var i = 0; i < remainingFaces.length; i++)
		{
			if(scope.getNoVerticesInCommon(parent,remainingFaces[i]) >= 2)
			{
				children.push(allFaces.indexOf(remainingFaces[i]));
			}
		}
		return children;
	};
	this.dot = function(v1,v2)
	{
		return v1[0]*v2[0]+v1[1]*v2[1]+v1[2]*v2[2];
	};
	this.subtract = function(v1,v2)
	{
		var result = [v1[0]-v2[0],
					v1[1]-v2[1],
					v1[2]-v2[2]];
		return result;
	};

	this.init = function(flatGeom)
	{
		/*------ Create the mesh tree --------*/
		this.faceRoot = scope.createTreeNode(flatGeom);

		/*----- Create Unflattened Mesh Lookup ------*/
		for(var i = 0; i < flatGeom.vertices.length; i++)
		{
			this.unflattenedVertices[i] = {x: flatGeom.vertices[i].x,
											y: flatGeom.vertices[i].y,
											z: flatGeom.vertices[i].z};
			this.flattenedVertices[i] = {x: flatGeom.vertices[i].x,
											y: flatGeom.vertices[i].y,
											z: flatGeom.vertices[i].z};
		}

		/*------ Rebuild mesh (first face is manually flattened) --------*/
		this.flattenedVertices[flatGeom.faces[scope.faceRoot.index].a].z = 0;
		this.flattenedVertices[flatGeom.faces[scope.faceRoot.index].b].z = 0;
		this.flattenedVertices[flatGeom.faces[scope.faceRoot.index].c].z = 0;

		this.alteredVertices.push(flatGeom.faces[scope.faceRoot.index].a);
		this.alteredVertices.push(flatGeom.faces[scope.faceRoot.index].b);
		this.alteredVertices.push(flatGeom.faces[scope.faceRoot.index].c);

		for(var i = 0; i < scope.faceRoot.leaves.length; i++)
		{
			scope.rebuildNode(scope.faceRoot.leaves[i], flatGeom.faces, this.flattenedVertices);
		}
	};

	this.init(flatGeom);
}

MESHFLATTEN.Flatten.prototype.constructor = MESHFLATTEN.Flatten;