-- Prove2me | Theorems.Thm_BroughanRH_nicolasUpper
-- name    : BroughanRH.nicolasUpper
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:14:07.187864+00:00
-- url     : https://prove2.me/theorems/8770703f-88bf-44d0-8781-7da88eb6ac2f
-- title:
--   Nicolas’s strict tail bound
-- statement:
--   Beyond and including the product of primes through $1591883$, the normalized error is strictly smaller than its limit superior.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 5.34 (2). https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem nicolasUpper :
    let c (n : ℕ) : ℝ := ((n : ℝ) / (n.totient : ℝ) - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) * Real.sqrt (Real.log n)
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    ∀ n : ℕ, primorial 1591883 ≤ n → c n < Real.exp Real.eulerMascheroniConstant * (2 + β) := by sorry

end BroughanRH
