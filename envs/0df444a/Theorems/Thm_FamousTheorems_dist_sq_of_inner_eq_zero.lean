-- Prove2me | Theorems.Thm_FamousTheorems_dist_sq_of_inner_eq_zero
-- name    : FamousTheorems.dist_sq_of_inner_eq_zero
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:55:21.945447+00:00
-- url     : https://prove2.me/theorems/47f5fd3c-232f-4258-a99f-1d1560031284
-- title:
--   The Pythagorean theorem (inner product form)
-- statement:
--   **The Pythagorean theorem** in an inner product space. If $\langle u, v \rangle = 0$ then $\lVert u - v\rVert^2 = \lVert u\rVert^2 + \lVert v\rVert^2$. Stated this way the theorem is the polarisation identity with the cross term deleted, which is precisely what orthogonality provides -- so Pythagoras is not a fact about triangles but about inner products, and holds in any dimension and in infinite-dimensional Hilbert spaces. It is the computation behind orthogonal decompositions, Bessel's inequality and Parseval's identity. **Formalization note.** The hypothesis is vanishing of the real inner product and distances are squared. The result is Mathlib's `dist_sq_of_inner_eq_zero`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem dist_sq_of_inner_eq_zero :
    ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {a b p : P}, 
    inner ℝ (p -ᵥ a) (b -ᵥ a) = 0 → dist p b ^ 2 = dist p a ^ 2 + dist a b ^ 2 := by sorry

end FamousTheorems
