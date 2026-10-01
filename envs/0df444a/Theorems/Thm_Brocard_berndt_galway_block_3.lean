-- Prove2me | Theorems.Thm_Brocard_berndt_galway_block_3
-- name    : Brocard.berndt_galway_block_3
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T01:37:06.291884+00:00
-- url     : https://prove2.me/theorems/21ef3ac9-9ad9-47e7-a5bd-c036561f0b32
-- title:
--   No solutions of $n!+1=m^2$ with $3\cdot 10^8 \le n < 4\cdot 10^8$
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$3 \cdot 10^8 \le n < 4 \cdot 10^8.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   This is block number 3 of the ten blocks of length $10^8$ into which the Berndt–Galway search range $n < 10^9$ is divided.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard–Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), 41–42 (computer search for n < 10^9); one of ten blocks of the milestone Brocard.berndt_galway_search.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_block_3 (n m : ℕ) (h1 : 3 * 10 ^ 8 ≤ n) (h2 : n < 4 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
