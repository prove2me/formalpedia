-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_001
-- name    : Brocard.berndt_galway_group_001
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:25:14.273413+00:00
-- url     : https://prove2.me/theorems/527f9630-9e9a-4206-8f38-0eb08a008220
-- title:
--   No solutions of $n!+1=m^2$ with $8 \le n < 8453244$ (Berndt-Galway search, group 1 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$8 \le n < 8453244.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 1 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 1 of 12 of block 0, `Brocard.berndt_galway_block_0`); it is proved from its 47 consecutive chunks (chunks 1 to 47 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_0`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_001 (n m : ℕ) (h1 : 8 ≤ n) (h2 : n < 8453244) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
