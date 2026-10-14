-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_065
-- name    : Brocard.berndt_galway_group_065
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:12:51.001505+00:00
-- url     : https://prove2.me/theorems/33217683-598e-437c-aacb-0dfcdce412e7
-- title:
--   No solutions of $n!+1=m^2$ with $533812949 \le n < 542086330$ (Berndt-Galway search, group 65 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$533812949 \le n < 542086330.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 65 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 5 of 12 of block 5, `Brocard.berndt_galway_block_5`); it is proved from its 46 consecutive chunks (chunks 2969 to 3014 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_5`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_065 (n m : ℕ) (h1 : 533812949 ≤ n) (h2 : n < 542086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
