-- Prove2me | Theorems.Thm_CubicP3Partition_root_problem
-- name    : CubicP3Partition.root_problem
-- status  : Open
-- author  : @hao jia
-- created : 2026-09-07T03:08:31.29924+00:00
-- url     : https://prove2.me/theorems/66451406-59ff-4a7d-b900-aa5ccca8c783
-- title:
--   OPG-46613: $P_3$-partitions of cubic 3-connected graphs
-- statement:
--   Let $V$ be a finite vertex type and let $G$ be a finite simple graph on $V$. Assume that every vertex of $G$ has degree three, deletion of any set of at most two vertices leaves a connected induced graph, $|V|\ge4$, and the number of vertices is divisible by three. Then the vertices can be partitioned into noninduced paths of length two:
--
--   $$
--   \operatorname{Cubic}(G)\land\operatorname{ThreeVertexConnected}(G)\land 3\mid |V|
--   \quad\Longrightarrow\quad
--   \operatorname{Nonempty}(\operatorname{P3Factor}(G)).
--   $$
--
--   Equivalently, when $|V|=3k$, the factor consists of $k$ pairwise vertex-disjoint three-vertex paths covering every vertex. This is the mission's open main goal; no candidate milestone is presented as a proof of it.
-- source:
--   UnsolvedMath, OPG-46613, https://www.unsolvedmath.com/problems/OPG-46613; see also A. Kelmans, https://arxiv.org/abs/0910.2766v2, p. 3, Problem 1.10, and pp. 7–8, Theorem 3.1 claim (z1).

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

/-- The divisible-order form of the cubic three-connected P3-packing problem. -/
theorem root_problem {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hCubic : Cubic G) (hConnected : ThreeVertexConnected G)
    (hOrder : 3 ∣ Fintype.card V) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
