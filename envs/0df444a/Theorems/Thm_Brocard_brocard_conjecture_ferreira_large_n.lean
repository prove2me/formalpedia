-- Prove2me | Theorems.Thm_Brocard_brocard_conjecture_ferreira_large_n
-- name    : Brocard.brocard_conjecture.ferreira_large_n
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:52:16.136127+00:00
-- url     : https://prove2.me/theorems/2322024f-f4e5-46a4-95c3-203801bda643
-- title:
--   Brocard's conjecture holds for all sufficiently large n (Ferreira)
-- statement:
--   There is an $N$ such that for every $n \ge N$, writing $p_n$ for the $n$-th prime (0-indexed: $p_0 = 2$), there are at least four primes $q$ with $p_n^2 < q < p_{n+1}^2$.
-- source:
--   L. A. Ferreira, Real exponential sums over primes and prime gaps, arXiv:2307.08725 (2023); statement as in Formal Conjectures, BrocardConjecture.lean, `brocard_conjecture.ferreira_large_n`

import Mathlib
open Finset Filter

namespace Brocard

theorem brocard_conjecture.ferreira_large_n : ∀ᶠ n in atTop,
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card := by sorry

end Brocard
