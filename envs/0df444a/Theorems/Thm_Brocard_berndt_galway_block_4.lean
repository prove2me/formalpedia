-- Prove2me | Theorems.Thm_Brocard_berndt_galway_block_4
-- name    : Brocard.berndt_galway_block_4
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T01:37:09.650994+00:00
-- url     : https://prove2.me/theorems/e6af5f08-6c81-4c65-826d-9c95f56e0d1c
-- title:
--   No solutions of $n!+1=m^2$ with $4\cdot 10^8 \le n < 5\cdot 10^8$
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$4 \cdot 10^8 \le n < 5 \cdot 10^8.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   This is block number 4 of the ten blocks of length $10^8$ into which the Berndt–Galway search range $n < 10^9$ is divided.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard–Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), 41–42 (computer search for n < 10^9); one of ten blocks of the milestone Brocard.berndt_galway_search.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_block_4 (n m : ℕ) (h1 : 4 * 10 ^ 8 ≤ n) (h2 : n < 5 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
