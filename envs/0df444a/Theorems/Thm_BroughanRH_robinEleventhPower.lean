-- Prove2me | Theorems.Thm_BroughanRH_robinEleventhPower
-- name    : BroughanRH.robinEleventhPower
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:18:31.629956+00:00
-- url     : https://prove2.me/theorems/0e5c0279-29ef-454c-b4dd-8892bdf84040
-- title:
--   Robin’s inequality for multiples of eleventh prime powers
-- statement:
--   For every integer $n>2$ divisible by an eleventh prime power, $\sigma(n)<e^\gamma n\log\log n$. The range includes the two exceptional-size inputs $2048$ and $4096$.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Cor. 8.17. https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem robinEleventhPower :
    ∀ n : ℕ, 2 < n → (∃ p : ℕ, p.Prime ∧ p^11 ∣ n) → ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by sorry

end BroughanRH
