-- Prove2me | Theorems.Thm_BroughanRH_nicolasExplicit
-- name    : BroughanRH.nicolasExplicit
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:17:53.712585+00:00
-- url     : https://prove2.me/theorems/725d574e-2961-466b-9d3e-33f8e279d2b1
-- title:
--   Nicolas’s explicit upper bound for the reciprocal totient
-- statement:
--   The explicit upper bound for $n/\varphi(n)$ holds from the primorial $N_{120569}$ onward.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Cor. 5.35. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem nicolasExplicit :
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    ∀ n : ℕ, primorial 1591883 ≤ n →
      (n : ℝ)/n.totient < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)
        + Real.exp Real.eulerMascheroniConstant * (2+β) / Real.sqrt (Real.log n) := by sorry

end BroughanRH
