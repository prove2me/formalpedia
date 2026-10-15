-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_114
-- name    : Brocard.berndt_galway_group_114
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:06:21.482994+00:00
-- url     : https://prove2.me/theorems/10f8f7ab-3f95-4d57-8c7e-a930d05bb22d
-- title:
--   No solutions of $n!+1=m^2$ with $942086330 \le n < 950359712$ (Berndt-Galway search, group 114 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$942086330 \le n < 950359712.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 114 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 6 of 12 of block 9, `Brocard.berndt_galway_block_9`); it is proved from its 46 consecutive chunks (chunks 5239 to 5284 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_9`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_114 (n m : ℕ) (h1 : 942086330 ≤ n) (h2 : n < 950359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
