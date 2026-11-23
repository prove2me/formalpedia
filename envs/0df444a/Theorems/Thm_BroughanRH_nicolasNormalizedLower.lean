-- Prove2me | Theorems.Thm_BroughanRH_nicolasNormalizedLower
-- name    : BroughanRH.nicolasNormalizedLower
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:22.347799+00:00
-- url     : https://prove2.me/theorems/2266af3b-9594-4722-b21f-93ba7098f4f6
-- title:
--   Uniform lower bound on Nicolas’s normalized error
-- statement:
--   From $x=37$ onward, the normalized prime-count discrepancy is at least $2-\beta$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III §1.7 (3). https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem nicolasNormalizedLower :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let A (x : ℝ) := (li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * (Real.log x)^2 / Real.sqrt x
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    ∀ x : ℝ, 37 ≤ x → 2 - β ≤ A x := by sorry

end BroughanRH
