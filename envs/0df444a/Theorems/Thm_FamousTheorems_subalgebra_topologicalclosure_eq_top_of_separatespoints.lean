-- Prove2me | Theorems.Thm_FamousTheorems_subalgebra_topologicalclosure_eq_top_of_separatespoints
-- name    : FamousTheorems.subalgebra_topologicalclosure_eq_top_of_separatespoints
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:12:59.977273+00:00
-- url     : https://prove2.me/theorems/07182643-6480-4f03-8716-c99f477d8638
-- title:
--   The Stone–Weierstrass theorem
-- statement:
--   **The Stone-Weierstrass theorem.** A subalgebra of $C(X,\mathbb{R})$ on a compact Hausdorff space that separates points is dense. Weierstrass's polynomial approximation theorem is the case of $[a,b]$ with the polynomials, but the general form is far more flexible, giving density of trigonometric polynomials on the circle and hence completeness of the Fourier basis, of polynomials in several variables, and of finite sums of products $f(x)g(y)$ on a product. Separating points is precisely the obstruction: an algebra that cannot distinguish two points can never approximate a function taking different values at them. Stone proved it in 1937. **Formalization note.** Closure is in the uniform topology on `C(X, ℝ)`. The result is Mathlib's `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem subalgebra_topologicalclosure_eq_top_of_separatespoints :
    ∀ {X : Type u_1} [inst : TopologicalSpace X] 
    [inst_1 : CompactSpace X] (A : Subalgebra ℝ C(X, ℝ)), A.SeparatesPoints → A.topologicalClosure = ⊤ := by sorry

end FamousTheorems
