-- Prove2me | Theorems.Thm_Brocard_brocard_conjecture
-- name    : Brocard.brocard_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:56:49.042464+00:00
-- url     : https://prove2.me/theorems/d18dc170-ed22-41d9-934b-d199f8ebaa03
-- title:
--   Brocard's conjecture
-- statement:
--   For every $n \ge 1$, writing $p_n$ for the $n$-th prime with 0-based indexing ($p_0 = 2$, $p_1 = 3$, $p_2 = 5$, …), there are at least four primes $q$ with $p_n^2 < q < p_{n+1}^2$. In the usual 1-based indexing this is Brocard's conjecture: for all $n \ge 2$ there are at least four primes between $p_n^2$ and $p_{n+1}^2$.
-- source:
--   Brocard's conjecture, https://en.wikipedia.org/wiki/Brocard%27s_conjecture ; statement as in Formal Conjectures, BrocardConjecture.lean, `brocard_conjecture`

import Mathlib
open Finset Filter

namespace Brocard

theorem brocard_conjecture (n : ℕ) (hn : 1 ≤ n) :
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card := by sorry

end Brocard
