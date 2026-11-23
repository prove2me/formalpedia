-- Prove2me | Theorems.Thm_BroughanRH_nicolasPrimeCounting
-- name    : BroughanRH.nicolasPrimeCounting
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:02.054329+00:00
-- url     : https://prove2.me/theorems/d1666604-d310-4724-a058-d024168a36e5
-- title:
--   Nicolas’s inequality for the prime count
-- statement:
--   For every real $x\ge11$, the prime count is strictly below the principal-value logarithmic integral at $\vartheta(x)$. The convergent exponential-integral series fixes the additive constant.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III Thm. 1.17. https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem nicolasPrimeCounting :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    ∀ x : ℝ, 11 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < li (Chebyshev.theta x) := by sorry

end BroughanRH
