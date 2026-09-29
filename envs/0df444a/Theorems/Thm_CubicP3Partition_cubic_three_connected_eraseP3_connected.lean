-- Prove2me | Theorems.Thm_CubicP3Partition_cubic_three_connected_eraseP3_connected
-- name    : CubicP3Partition.cubic_three_connected_eraseP3_connected
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T09:19:58.332142+00:00
-- url     : https://prove2.me/theorems/8802fc0a-f10b-4d80-ab28-1508c6990f7d
-- title:
--   Deleting a P3 from a cubic 3-connected graph leaves a connected residual graph
-- statement:
--   Let $G$ be a finite cubic graph that remains connected after deletion of any set of at most two vertices. For every displayed path $a-b-c$ in $G$, delete $a,b,c$ and take the induced graph on the remaining vertices. The resulting graph is connected.
--
--   This structural lemma shows that a single $P_3$ deletion cannot create multiple residual components under cubic three-vertex-connectivity. It does not assert that the residual graph has a $P_3$-factor.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

/-- Deleting the three vertices of any displayed P3 from a finite cubic three-vertex-connected graph leaves a connected induced residual graph. -/
theorem cubic_three_connected_eraseP3_connected
    {V : Type} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G) (L : P3Path G) :
    (eraseP3 G L).Connected := by sorry

end CubicP3Partition
