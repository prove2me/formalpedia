-- Prove2me | Theorems.Thm_Brocard_berndt_galway_block_5
-- name    : Brocard.berndt_galway_block_5
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T01:37:11.163781+00:00
-- url     : https://prove2.me/theorems/6b4ce1b0-e809-4a14-9c63-6cc2d9dc95e1
-- title:
--   No solutions of $n!+1=m^2$ with $5\cdot 10^8 \le n < 6\cdot 10^8$
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$5 \cdot 10^8 \le n < 6 \cdot 10^8.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   This is block number 5 of the ten blocks of length $10^8$ into which the Berndt–Galway search range $n < 10^9$ is divided.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard–Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), 41–42 (computer search for n < 10^9); one of ten blocks of the milestone Brocard.berndt_galway_search.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_block_5 (n m : ℕ) (h1 : 5 * 10 ^ 8 ≤ n) (h2 : n < 6 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
