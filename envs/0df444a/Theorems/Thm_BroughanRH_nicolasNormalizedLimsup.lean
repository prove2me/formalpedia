-- Prove2me | Theorems.Thm_BroughanRH_nicolasNormalizedLimsup
-- name    : BroughanRH.nicolasNormalizedLimsup
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:08.08032+00:00
-- url     : https://prove2.me/theorems/595becd4-bef9-4c18-aed6-97e46f75b44c
-- title:
--   Nicolas’s upper limit for the normalized prime-count error
-- statement:
--   The limit superior of the normalized discrepancy is at most $2+\beta$. [Source](https://doi.org/10.1007/978-3-319-68376-8_32).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III §1.7 (1). https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem nicolasNormalizedLimsup :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let A (x : ℝ) := (li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * (Real.log x)^2 / Real.sqrt x
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    Filter.limsup (fun x : ℝ => (A x : EReal)) Filter.atTop ≤ ((2 + β : ℝ) : EReal) := by sorry

end BroughanRH
