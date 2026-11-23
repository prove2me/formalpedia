-- Prove2me | Theorems.Thm_BroughanRH_nicolasNormalizedMax
-- name    : BroughanRH.nicolasNormalizedMax
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:22.977423+00:00
-- url     : https://prove2.me/theorems/7f3d3cdd-cda1-403e-8cc3-d3e396bd43e9
-- title:
--   Maximum of Nicolas’s normalized discrepancy
-- statement:
--   The normalized discrepancy on $x\ge2$ attains a global maximum at $3643$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III §1.7 (4). https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem nicolasNormalizedMax :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let A (x : ℝ) := (li (Chebyshev.theta x) - (Nat.primeCounting ⌊x⌋₊ : ℝ)) * (Real.log x)^2 / Real.sqrt x
    ∀ x : ℝ, 2 ≤ x → A x ≤ A 3643 := by sorry

end BroughanRH
