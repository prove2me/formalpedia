-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_003
-- name    : Brocard.berndt_galway_group_003
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:56:24.818779+00:00
-- url     : https://prove2.me/theorems/4ca48b28-4803-4cd6-9b30-0d177c7d9cb8
-- title:
--   No solutions of $n!+1=m^2$ with $16906481 \le n < 25359718$ (Berndt-Galway search, group 3 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$16906481 \le n < 25359718.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 3 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 3 of 12 of block 0, `Brocard.berndt_galway_block_0`); it is proved from its 47 consecutive chunks (chunks 95 to 141 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_0`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_003 (n m : ℕ) (h1 : 16906481 ≤ n) (h2 : n < 25359718) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
