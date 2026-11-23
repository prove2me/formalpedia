-- Prove2me | Theorems.Thm_BroughanRH_nicolasMax
-- name    : BroughanRH.nicolasMax
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:14:58.286259+00:00
-- url     : https://prove2.me/theorems/1d9b1e03-6a63-44a0-aedd-a57c2bb88126
-- title:
--   The maximum of the normalized totient error
-- statement:
--   Among all integers $n\ge2$, the product of the primes through $317$ attains the global maximum of the normalized error.
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, I Thm. 5.34 (3). https://doi.org/10.1017/9781108178228

import Mathlib

namespace BroughanRH

theorem nicolasMax :
    let c (n : ℕ) : ℝ := ((n : ℝ) / (n.totient : ℝ) - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) * Real.sqrt (Real.log n)
    ∀ n : ℕ, 2 ≤ n → c n ≤ c (primorial 317) := by sorry

end BroughanRH
