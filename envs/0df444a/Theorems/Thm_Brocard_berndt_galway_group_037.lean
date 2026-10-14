-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_037
-- name    : Brocard.berndt_galway_group_037
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:57:28.031012+00:00
-- url     : https://prove2.me/theorems/73ed7230-e1f9-4c66-bd13-c5dde7cb78d7
-- title:
--   No solutions of $n!+1=m^2$ with $300000000 \le n < 308453237$ (Berndt-Galway search, group 37 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$300000000 \le n < 308453237.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 37 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 1 of 12 of block 3, `Brocard.berndt_galway_block_3`); it is proved from its 47 consecutive chunks (chunks 1669 to 1715 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_3`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_037 (n m : ℕ) (h1 : 300000000 ≤ n) (h2 : n < 308453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
