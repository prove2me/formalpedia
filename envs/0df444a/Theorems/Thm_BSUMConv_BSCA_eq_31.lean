-- Prove2me | Theorems.Thm_BSUMConv_BSCA_eq_31
-- name    : BSUMConv.BSCA.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:48.499388+00:00
-- url     : https://prove2.me/theorems/d25b082a-e2fc-4e46-a0cc-5fc5e61dbaa9
-- title:
--   (31), p. 17 — block approximation minimizers give descent directions
-- statement:
--   Let $x\in X$, let $y$ differ from $x$ only in block $i$, and suppose $y_i$ minimizes the convex approximation $h_i(\cdot,x)$ over $X_i$. If the approximation has the same first-order directional derivative as the continuously differentiable objective $f$ at $x$, then
--   $$f'(x;y-x)=h_i'(x_i,x;y_i-x_i)\le 0.$$
--
--   This is the descent relation used to justify the BSCA Armijo search.
--
--   **Formalization Note** The derivative of $h_i$ is the extended-real lower directional derivative; the derivative of $f$ is its Fréchet derivative, equal to the paper's lower directional derivative under the $C^1$ hypothesis.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 17, (31)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSCA_Setting

namespace BSUMConv.BSCA

open TsengBCD.Stationary

/-- Display (31), p. 17: the block-minimizing direction is a descent direction. -/
theorem eq_31 {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (h : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (hC1 : ContDiff ℝ 1 f)
    (hmatch : FirstOrderAgreement Xs f h)
    (x y : X n) (hx : x ∈ BSUMConv.BSUM.Xset Xs) (i : Fin N)
    (hy : y i ∈ Xs i)
    (hother : ∀ k, k ≠ i → y k = x k)
    (hmin : ∀ w ∈ Xs i, h i (y i) x ≤ h i w x)
    (hconv : ConvexOn ℝ (Xs i) (fun xi => h i xi x)) :
    ((fderiv ℝ f x (y - x) : ℝ) : EReal) =
        dirDeriv (fun yi => (h i yi x : EReal)) (x i) (y i - x i) ∧
      fderiv ℝ f x (y - x) ≤ 0 := by sorry

end BSUMConv.BSCA
