-- Prove2me | Theorems.Thm_AndricaConjecture_andrica_up_to_maximal_gap_80
-- name    : AndricaConjecture.andrica_up_to_maximal_gap_80
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:51.11999+00:00
-- url     : https://prove2.me/theorems/0feb5280-c4c3-483b-98c8-85f689aab724
-- title:
--   Andrica's inequality through the $80$th maximal prime gap
-- statement:
--   Let $p_n=$ `Nat.nth Nat.Prime n` be the $n$th prime in zero-based indexing. If $p_n\le 18{,}361{,}375{,}334{,}787{,}046{,}697$, then $\sqrt{p_{n+1}}-\sqrt{p_n}<1$, where the square roots are real. This is a known computational theorem: the bound is the prime at which the $80$th first-occurrence maximal prime gap begins, and the comparison is the one recorded by Visser (2018, §6), building on complete gap computations such as that of Oliveira e Silva, Herzog, and Pardi up to $4\cdot 10^{18}$.
-- source:
--   Matt Visser, Variants on Andrica's conjecture with and without the Riemann hypothesis, Mathematics 6 (2018), no. 12, 289, §6, with p*_80 = 18,361,375,334,787,046,697, https://arxiv.org/abs/1804.02500 ; underlying complete gaps up to 4·10^18 in Oliveira e Silva, Herzog, and Pardi, Math. Comp. 83 (2014), 2033–2060, https://doi.org/10.1090/S0025-5718-2013-02787-1

import Mathlib

namespace AndricaConjecture
theorem andrica_up_to_maximal_gap_80 (n : Nat)
    (hn : Nat.nth Nat.Prime n ≤ 18361375334787046697) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real) -
      Real.sqrt (Nat.nth Nat.Prime n : Real) < 1 := by sorry
end AndricaConjecture
