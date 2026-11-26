-- Prove2me | Theorems.Thm_AndricaConjecture_andrica_conjecture
-- name    : AndricaConjecture.andrica_conjecture
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:52.606264+00:00
-- url     : https://prove2.me/theorems/8d4c82e1-a5fb-53af-acd7-f8d865613818
-- title:
--   Andrica's conjecture: $\sqrt{p_{n+1}}-\sqrt{p_n}<1$
-- statement:
--   Let $p_n=$ `Nat.nth Nat.Prime n` denote the $n$th prime in Mathlib's zero-based indexing, so that $p_0=2$ and $p_1=3$. Then for every natural number $n$,
--   $$
--   \sqrt{p_{n+1}}-\sqrt{p_n}<1,
--   $$
--   where the square roots are the nonnegative real square roots. This is Andrica's conjecture, which remains open. In the classical one-based numbering $p_1=2$, $p_2=3$, $\ldots$, the same inequality is the assertion $\sqrt{p_{n+1}}-\sqrt{p_n}<1$ for all $n\ge 1$; the Lean statement covers every consecutive pair, including the first gap.
-- source:
--   Dorin Andrica, Note on a conjecture in prime number theory, Studia Univ. Babeș-Bolyai Math. 31 (1986), no. 4, 44–48, https://zbmath.org/0623.10030

import Mathlib

namespace AndricaConjecture
theorem andrica_conjecture (n : Nat) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real) -
      Real.sqrt (Nat.nth Nat.Prime n : Real) < 1 := by sorry
end AndricaConjecture
