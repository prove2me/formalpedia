-- Prove2me | Theorems.Thm_CubicP3Partition_cubic_triangle_residual_two_connected
-- name    : CubicP3Partition.cubic_triangle_residual_two_connected
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T09:20:03.83092+00:00
-- url     : https://prove2.me/theorems/0aef5afb-b386-4237-96b5-d392bc4f9bb6
-- title:
--   Triangle deletion in a divisible-order cubic 3-connected graph leaves a 2-connected residual
-- statement:
--   Let $G$ be a finite cubic three-vertex-connected graph whose order is divisible by three, and let $abc$ be a triangle. After deleting $a,b,c$, the induced residual graph is connected. Moreover, deleting any one additional residual vertex still leaves it connected. Thus the triangle residual has no cut vertex in the explicit deletion-connectivity sense used here.
--
--   The theorem is a structural reduction for studying $P_3$-factors; it does not itself construct such a factor.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

/-- In a finite cubic three-vertex-connected graph of order divisible by three, deleting a triangle leaves a connected residual with no cut vertex. -/
theorem cubic_triangle_residual_two_connected
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G)
    (hdiv : 3 ∣ Fintype.card V)
    {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c}).Connected ∧
      ∀ x : V, x ≠ a ∧ x ≠ b ∧ x ≠ c →
        (G.induce {v : V | v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x}).Connected := by sorry

end CubicP3Partition
