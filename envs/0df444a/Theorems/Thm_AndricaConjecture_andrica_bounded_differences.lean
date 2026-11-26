-- Prove2me | Theorems.Thm_AndricaConjecture_andrica_bounded_differences
-- name    : AndricaConjecture.andrica_bounded_differences
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:50.783192+00:00
-- url     : https://prove2.me/theorems/f48b7f95-dc1e-58d2-94ee-1de166c28dff
-- title:
--   Andrica differences are uniformly bounded
-- statement:
--   There exists a real constant $C$ such that $\sqrt{p_{n+1}}-\sqrt{p_n}<C$ for every natural number $n$, where $p_n=$ `Nat.nth Nat.Prime n` is the $n$th prime in zero-based indexing and the square roots are real. This is a weaker open statement than Andrica's conjecture (the case $C=1$). It is equivalent to $p_{n+1}-p_n=O(\sqrt{p_n})$, and it is not implied by the Baker–Harman–Pintz bound $p_{n+1}-p_n\ll p_n^{0.525}$.
-- source:
--   Weaker open form of Andrica's conjecture (uniform boundedness of √p_{n+1}−√p_n). For the comparison with proved gap estimates see Baker, Harman, and Pintz, The difference between consecutive primes, II, Proc. Lond. Math. Soc. (3) 83 (2001), 532–562, https://doi.org/10.1112/plms/83.3.532, and Visser, Mathematics 6 (2018), 289, https://arxiv.org/abs/1804.02500

import Mathlib

namespace AndricaConjecture
theorem andrica_bounded_differences :
    ∃ C : Real, ∀ n : Nat,
      Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real) -
        Real.sqrt (Nat.nth Nat.Prime n : Real) < C := by sorry
end AndricaConjecture
