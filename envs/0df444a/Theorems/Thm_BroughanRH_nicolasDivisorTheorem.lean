-- Prove2me | Theorems.Thm_BroughanRH_nicolasDivisorTheorem
-- name    : BroughanRH.nicolasDivisorTheorem
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:29:43.881014+00:00
-- url     : https://prove2.me/theorems/a712acc8-a0c9-4849-b594-5957fe91c128
-- title:
--   Nicolas’s divisor-count bound in the numbered theorem
-- statement:
--   Equation (2.9) on p. 79 gives the divisor-count estimate from $n>122522400$ with $\sqrt{\log\log n}$ in the first correction. The introductory version on p. 37 uses $\sqrt{\log n}$ there. Each displayed formula has its own card.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III Thm. 2.24. https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem nicolasDivisorTheorem :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    let β₂ := Real.log (3/2) / Real.log 2
    let β₃ := Real.log (4/3) / Real.log 2
    let F (t : ℝ) := li t + β₂ * li (t^β₂) - t^β₂ / Real.log t
    ∀ n : ℕ, 122522400 < n →
      let t := Real.log (n : ℝ)
      Real.log (n.divisors.card : ℝ) / Real.log 2 ≤ F t -
        (2-β) * Real.sqrt (Real.log t) / t^2 - 5.12 * Real.sqrt t / (Real.log t)^3 +
        1.52 * t^β₃ / Real.log t := by sorry

end BroughanRH
