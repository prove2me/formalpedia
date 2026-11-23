-- Prove2me | Theorems.Thm_BroughanRH_nicolasNormalizedLiminf
-- name    : BroughanRH.nicolasNormalizedLiminf
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:07.507851+00:00
-- url     : https://prove2.me/theorems/a4a4ae96-ebe7-4694-8208-dab4c242e6e1
-- title:
--   Nicolas’s lower limit for the normalized prime-count error
-- statement:
--   The limit inferior is at least $2-\beta$. This follows the lower bound in Nicolas’s Theorem 1.1, formula (1.7). Volume III, p. 34, prints the opposite inequality. [Source](https://doi.org/10.1007/978-3-319-68376-8_32).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III §1.7 (2). https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem nicolasNormalizedLiminf :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let A (x : ℝ) := (li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * (Real.log x)^2 / Real.sqrt x
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    ((2 - β : ℝ) : EReal) ≤ Filter.liminf (fun x : ℝ => (A x : EReal)) Filter.atTop := by sorry

end BroughanRH
