-- Prove2me | Theorems.Thm_ConvexOptAlg_LowerBounds_thm_3_14_norm_bound
-- name    : ConvexOptAlg.LowerBounds.thm_3_14_norm_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:44:29.487515+00:00
-- url     : https://prove2.me/theorems/13184497-b091-4fff-b0c1-cef44958a28f
-- title:
--   Proof of Theorem 3.14, p. 283 — ‖x*_k‖² = Σᵢ (i/(k+1))² ≤ (k+1)/3
-- statement:
--   Let $k\le n$ and let $x^*_k\in\mathbb R^n$ have coordinates $x^*_k(i)=1-\frac{i}{k+1}$ for $i\le k$ and $0$ beyond. Then
--   $$\|x^*_k\|^2=\sum_{i=1}^{k}\Bigl(1-\frac{i}{k+1}\Bigr)^2=\sum_{i=1}^{k}\Bigl(\frac{i}{k+1}\Bigr)^2\le\frac{k+1}{3}.$$
--
--   The bound controls the distance $\|x_1-x^*\|$ from the starting point $x_1=0$ to the minimizer in Theorem 3.14.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 283

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.LowerBounds

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 283: for `k ≤ n`,
`‖x*_k‖² = Σ_{i=1}^{k} (1 − i/(k+1))² = Σ_{i=1}^{k} (i/(k+1))² ≤ (k+1)/3`. -/
theorem thm_3_14_norm_bound (n k : ℕ) (hkn : k ≤ n) :
    ‖xstarK n k‖ ^ 2 = ∑ i ∈ Finset.Icc 1 k, (1 - (i : ℝ) / ((k : ℝ) + 1)) ^ 2 ∧
      ∑ i ∈ Finset.Icc 1 k, (1 - (i : ℝ) / ((k : ℝ) + 1)) ^ 2 =
        ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) / ((k : ℝ) + 1)) ^ 2 ∧
      ∑ i ∈ Finset.Icc 1 k, ((i : ℝ) / ((k : ℝ) + 1)) ^ 2 ≤ ((k : ℝ) + 1) / 3 := by sorry

end ConvexOptAlg.LowerBounds
