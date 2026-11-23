-- Prove2me | Theorems.Thm_BroughanRH_matiyasevichInteger
-- name    : BroughanRH.matiyasevichInteger
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:29:09.309508+00:00
-- url     : https://prove2.me/theorems/c3f4ed90-78d5-491a-b88d-efb1e7ea8506
-- title:
--   Matiyasevich’s integer inequality
-- statement:
--   Matiyasevich’s inequality (25) holds for every positive integer, using the integer part of the binary logarithm of $\operatorname{lcm}(1,\ldots,n)$. The integer factor $d(n)$ uses equation (21) of the published 2020 version. [Source](https://doi.org/10.1016/j.tcs.2019.07.028).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, III Thm. 11.6. https://doi.org/10.1017/9781009384780

import Mathlib

namespace BroughanRH

theorem matiyasevichInteger :
    let evenFact (m : ℕ) := 2^m * m.factorial
    let d (n : ℕ) : ℤ := ∑ k ∈ Finset.Ico 1 n,
      (-1 : ℤ)^(k+1) * ((evenFact (n-1) / k : ℕ) : ℤ)
    let l (n : ℕ) := Nat.log2 ((Finset.Icc 1 n).lcm id)
    let f₀ (n : ℕ) := evenFact n / 2
    let f₃ (n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 2 n, (2*j+3)
    ∀ n : ℕ, 1 ≤ n → (Nat.primeCounting n : ℤ)^2 *
      (d n * (l n : ℤ) - (f₀ n : ℤ)) < (f₃ n : ℤ) := by sorry

end BroughanRH
