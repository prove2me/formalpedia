-- Prove2me | Theorems.Thm_CarmichaelConjecture_odd_not_unique
-- name    : CarmichaelConjecture.odd_not_unique
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:32.035202+00:00
-- url     : https://prove2.me/theorems/cd24aea4-4994-411e-8225-a6c4b6d21031
-- title:
--   Odd $n$ are never unique preimages of $\varphi$
-- statement:
--   If $n$ is an odd natural number, then there exists a natural number $m\neq n$ such that $\varphi(m)=\varphi(n)$, where $\varphi$ denotes Euler's totient function. (This is a known elementary theorem: one may take $m=2n$.)
-- source:
--   Standard identity φ(2n)=φ(n) for odd n; Mathlib lemma Nat.totient_two_mul_of_odd. See also Ford, The distribution of totients, Ramanujan J. 2 (1998), 67–151, §1.3, https://arxiv.org/abs/1104.3264

import Mathlib

namespace CarmichaelConjecture
theorem odd_not_unique {n : Nat} (hn : Odd n) :
    ∃ m, m ≠ n ∧ Nat.totient m = Nat.totient n := by sorry
end CarmichaelConjecture
