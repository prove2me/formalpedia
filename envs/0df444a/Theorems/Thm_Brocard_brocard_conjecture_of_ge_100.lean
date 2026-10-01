-- Prove2me | Theorems.Thm_Brocard_brocard_conjecture_of_ge_100
-- name    : Brocard.brocard_conjecture_of_ge_100
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T00:52:01.213831+00:00
-- url     : https://prove2.me/theorems/fd7ad7ee-f5e2-49d3-a5cf-44dca7ad02b7
-- title:
--   Brocard's conjecture for all indices $n \ge 100$
-- statement:
--   Write $p_n$ for the $n$-th prime with 0-based indexing ($p_0 = 2$, $p_1 = 3$, $p_2 = 5$, …, $p_{100} = 547$). For every index $n \ge 100$ there are at least four primes $q$ with
--   $$p_n^2 < q < p_{n+1}^2.$$
--   This is Brocard's conjecture restricted to consecutive prime pairs starting from $(p_{100}, p_{101}) = (547, 557)$; it is an explicit-threshold strengthening of the asymptotic statement ("for all sufficiently large $n$") and remains open.
-- source:
--   Brocard's conjecture, https://en.wikipedia.org/wiki/Brocard%27s_conjecture ; tail (indices ≥ 100) of the statement `brocard_conjecture` (Formal Conjectures, BrocardConjecture.lean).

import Mathlib
open Finset Filter

namespace Brocard

theorem brocard_conjecture_of_ge_100 (n : ℕ) (hn : 100 ≤ n) :
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card := by sorry

end Brocard
