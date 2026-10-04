-- Prove2me | Theorems.Thm_Conway99Formal_GridEndpointSubmission_endpoint_support_bounds
-- name    : Conway99Formal.GridEndpointSubmission.endpoint_support_bounds
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:38:43.514186+00:00
-- url     : https://prove2.me/theorems/9541f28e-9a8c-44e2-abc1-a4b9216f1a56
-- title:
--   Endpoint bounds for ordinary and exceptional vertices
-- statement:
--   Let $G$ be an actual strongly regular graph with parameters $(99,14,1,2)$, equipped with endpoint census data for the case in which the same graph has 858 unordered disjoint triangle pairs with two cross edges. Suppose the graph's trace-defect function has total 66, and its graph-derived prism census has 231 triangles and weighted prism sum 2200, with the stated seven-triangle incidence and per-triangle caps for vertices of trace defect zero. Then the number of zero-defect vertices is between 33 and 50, so the number of positive-defect vertices is between 49 and 66. All triangle counts, the endpoint count, and both vertex sets belong to the same graph.
-- source:
--   Conway99Formal.GridEndpoint.EndpointData.ordinary_and_exceptional_bounds, in formalization/2026-10-03/grid-endpoint/GridEndpoint.lean at integration commit a45708acebe3f397faccb1b646be906f24f23ee5. The endpoint is twoCrossCount G = 858; the exact graph-owned trace, triangle census, and local incidence fields are part of EndpointData. Formal-geometry QA receipt run-f9fd0a584ca5 passed on that integration revision.

import Mathlib
import Definitions.Def_grid_endpoint_data
open Finset SimpleGraph Conway99Formal.GridEndpoint

theorem Conway99Formal.GridEndpointSubmission.endpoint_support_bounds {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (D : Conway99Formal.GridEndpoint.EndpointData G) : 33 ≤ D.ordinary ∧ D.ordinary ≤ 50 ∧ 49 ≤ 99 - D.ordinary ∧ 99 - D.ordinary ≤ 66 := by sorry
