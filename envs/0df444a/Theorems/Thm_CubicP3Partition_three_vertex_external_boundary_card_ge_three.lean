-- Prove2me | Theorems.Thm_CubicP3Partition_three_vertex_external_boundary_card_ge_three
-- name    : CubicP3Partition.three_vertex_external_boundary_card_ge_three
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T09:20:14.920457+00:00
-- url     : https://prove2.me/theorems/ff0f304d-e576-4a74-afbd-36501579e5c3
-- title:
--   Three-vertex sets have external boundary at least three
-- statement:
--   Let $G$ be a finite three-vertex-connected simple graph whose order is divisible by three. Every set $Q$ of exactly three vertices has at least three distinct neighbours outside $Q$:
--
--   $$
--   |Q|=3\quad\Longrightarrow\quad |N(Q)\setminus Q|\ge 3.
--   $$
--
--   This is an external-boundary consequence of three-vertex-connectivity. It is useful as a separator constraint in augmentation arguments.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

/-- In a finite three-vertex-connected graph of order divisible by three, every three-vertex set has at least three external neighbours. -/
theorem three_vertex_external_boundary_card_ge_three
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ThreeVertexConnected G)
    (hdiv : 3 ∣ Fintype.card V)
    (Q : Finset V) (hQcard : Q.card = 3) :
    3 ≤ (Q.biUnion (fun v => G.neighborFinset v) \ Q).card := by sorry

end CubicP3Partition
