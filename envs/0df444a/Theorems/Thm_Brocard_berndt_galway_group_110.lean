-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_110
-- name    : Brocard.berndt_galway_group_110
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:33:14.547998+00:00
-- url     : https://prove2.me/theorems/055c96c5-6ff0-411c-b2ab-947e4fafe0a3
-- title:
--   No solutions of $n!+1=m^2$ with $908453237 \le n < 916906474$ (Berndt-Galway search, group 110 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$908453237 \le n < 916906474.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 110 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 2 of 12 of block 9, `Brocard.berndt_galway_block_9`); it is proved from its 47 consecutive chunks (chunks 5052 to 5098 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_9`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_110 (n m : ℕ) (h1 : 908453237 ≤ n) (h2 : n < 916906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
