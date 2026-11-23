-- Prove2me | Theorems.Thm_BroughanRH_nicolasDivisorCriterion
-- name    : BroughanRH.nicolasDivisorCriterion
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:21.816035+00:00
-- url     : https://prove2.me/theorems/50153282-5524-4833-8b74-efd2fe4fe4e8
-- title:
--   Nicolas’s explicit bound for the divisor count
-- statement:
--   Nicolas bounds the number of positive divisors for every integer $n>122{,}522{,}400$. Writing $t=\log n$, the first correction is $-(2-\tau)\sqrt{t}/(\log t)^2$. This follows the original equation (1.10). Equations (4.23) and (4.24) describe the positive oscillations if RH fails. [Nicolas, Corollary 1.2 and §4.5](https://wwwhomes.uni-bielefeld.de/achim/HCN/hcnHR.pdf).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III §2.1 and Thm. 2.24. Jean-Louis Nicolas, Highly Composite Numbers and the Riemann hypothesis, Cor. 1.2, eq. (1.10), and §4.5. https://wwwhomes.uni-bielefeld.de/achim/HCN/hcnHR.pdf

import Mathlib

namespace BroughanRH

theorem nicolasDivisorCriterion :
    let li (y : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log |Real.log y| + ∑' k : ℕ, (Real.log y)^(k+1) / (((k+1 : ℕ) : ℝ) * ((k+1).factorial : ℝ))
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    let β₂ := Real.log (3/2) / Real.log 2
    let β₃ := Real.log (4/3) / Real.log 2
    let F (t : ℝ) := li t + β₂ * li (t^β₂) - t^β₂ / Real.log t
    ∀ n : ℕ, 122522400 < n →
      let t := Real.log (n : ℝ)
      Real.log (n.divisors.card : ℝ) / Real.log 2 ≤ F t -
        (2-β) * Real.sqrt t / (Real.log t)^2 - 5.12 * Real.sqrt t / (Real.log t)^3 +
        1.52 * t^β₃ / Real.log t := by sorry

end BroughanRH
