-- Prove2me | Theorems.Thm_Brocard_brocard_conjecture_of_lt_100
-- name    : Brocard.brocard_conjecture_of_lt_100
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-01T00:51:49.360978+00:00
-- url     : https://prove2.me/theorems/05e1dcae-02da-4a0b-bf8d-c9c5d913a82f
-- title:
--   Brocard's conjecture for the indices $1 \le n < 100$ (finite verification)
-- statement:
--   Write $p_n$ for the $n$-th prime with 0-based indexing ($p_0 = 2$, $p_1 = 3$, $p_2 = 5$, …). For every index $n$ with $1 \le n < 100$ (that is, for all pairs of consecutive primes $(p_n, p_{n+1})$ from $(3,5)$ up to $(p_{99}, p_{100}) = (541, 547)$) there are at least four primes $q$ with
--   $$p_n^2 < q < p_{n+1}^2.$$
--   This is the finite initial range of Brocard's conjecture, a purely computational statement.
-- source:
--   Brocard's conjecture, https://en.wikipedia.org/wiki/Brocard%27s_conjecture ; finite initial segment of the statement `brocard_conjecture` (Formal Conjectures, BrocardConjecture.lean), split at index 100.

import Mathlib
open Finset Filter

namespace Brocard

theorem brocard_conjecture_of_lt_100 (n : ℕ) (hn : 1 ≤ n) (hn' : n < 100) :
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card := by sorry

end Brocard
