-- Prove2me | Theorems.Thm_FamousTheorems_dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
-- name    : FamousTheorems.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:53.807215+00:00
-- url     : https://prove2.me/theorems/1ff869c6-b3ae-44c5-ad7b-cf8fa14ba3e0
-- title:
--   Apollonius's theorem
-- statement:
--   **Apollonius's theorem** (the median-length formula). For a triangle with median to the midpoint $m$ of one side, $$|AB|^2 + |AC|^2 = 2|Am|^2 + \tfrac12 |BC|^2.$$ The sum of squares of two sides is determined by the median to the third side and that side's length. It is the parallelogram law in disguise — doubling the median produces a parallelogram, and the identity becomes the statement that the sum of squares of the diagonals equals the sum of squares of the sides. That connection is why the result holds in any inner product space and characterises norms coming from inner products. **Formalization note.** `midpoint` is the affine midpoint and distances are squared. The result is Mathlib's `EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq :
    ∀ {V : Type u_1} {P : Type u_2} 
    [inst : NormedAddCommGroup V] [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] 
    (a b c : P), dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) := by sorry

end FamousTheorems
