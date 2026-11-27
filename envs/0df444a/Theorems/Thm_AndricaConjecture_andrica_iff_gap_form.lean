-- Prove2me | Theorems.Thm_AndricaConjecture_andrica_iff_gap_form
-- name    : AndricaConjecture.andrica_iff_gap_form
-- status  : Proved
-- author  : @jakevej
-- created : 2026-11-27T03:01:04.453578+00:00
-- url     : https://prove2.me/theorems/daaa0229-7168-4c36-9d12-4bd32b6c33d1
-- title:
--   Andrica's inequality is equivalent to its gap form
-- statement:
--   Let $p_n$ denote the $n$th prime in Mathlib's zero-based indexing. Then for every $n$, $\sqrt{p_{n+1}}-\sqrt{p_n}<1$ if and only if $p_{n+1}-p_n<2\sqrt{p_n}+1$. This is a pure identity of real square roots: writing $s=\sqrt{p_n}$ and $t=\sqrt{p_{n+1}}$, both sides are equivalent to $t<s+1$, since $t^2-s^2=(t-s)(t+s)$ and $t^2=p_{n+1}$, $s^2=p_n$. It does not prove Andrica's conjecture itself, which remains open; it records the exact equivalence between the conjecture and its gap form, so that either form may be used in place of the other.\n\n**Formalization Note** The statement uses the same casts and indexing as the mission's gap-form milestone.
-- source:
--   Andrica, D., Note on a conjecture in prime number theory, Studia Sci. Math. Hungar. 21 (1986) 1-2; mission Andrica's conjecture on sqrt(p_{n+1})-sqrt(p_n), milestone Equivalent gap form of Andrica's inequality.

import Mathlib

namespace AndricaConjecture

/-- Andrica's inequality is equivalent to its gap form: for consecutive primes,
`√pₙ₊₁ - √pₙ < 1` if and only if `pₙ₊₁ - pₙ < 2√pₙ + 1`. -/
theorem andrica_iff_gap_form (n : Nat) :
    Real.sqrt (Nat.nth Nat.Prime (n + 1) : Real) -
        Real.sqrt (Nat.nth Nat.Prime n : Real) < 1 ↔
      (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : Real) <
        2 * Real.sqrt (Nat.nth Nat.Prime n : Real) + 1 := by
  sorry

end AndricaConjecture
