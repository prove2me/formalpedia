-- Prove2me | Theorems.Thm_BroughanRH_nicolasDivisorCount
-- name    : BroughanRH.nicolasDivisorCount
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:47.825411+00:00
-- url     : https://prove2.me/theorems/cceac978-ee6a-476e-a19f-d1da73843a5f
-- title:
--   Nicolas’s explicit bound for the divisor count
-- statement:
--   The explicit upper bound for $\log d(n)/\log 2$ holds for every integer $n>122522400$. This is Broughan’s fixed-$\tau$ version as printed on p. 37. Its first error term has denominator $(\log n)^2$. [Source](https://api.pageplace.de/preview/DT0400.9781009384773_A49234842/preview-9781009384773_A49234842.pdf#page=59).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III §2.1 (6). https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem nicolasDivisorCount :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    let β₂ := Real.log (3/2) / Real.log 2
    let β₃ := Real.log (4/3) / Real.log 2
    let F (t : ℝ) := li t + β₂ * li (t^β₂) - t^β₂ / Real.log t
    ∀ n : ℕ, 122522400 < n →
      let t := Real.log (n : ℝ)
      Real.log (n.divisors.card : ℝ) / Real.log 2 ≤ F t -
        (2-β) * Real.sqrt t / t^2 - 5.12 * Real.sqrt t / (Real.log t)^3 +
        1.52 * t^β₃ / Real.log t := by sorry

end BroughanRH
