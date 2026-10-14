-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_021
-- name    : Brocard.berndt_galway_group_021
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:26:36.525441+00:00
-- url     : https://prove2.me/theorems/6fee8b98-f3ed-4e13-ba9f-9e9f0732206f
-- title:
--   No solutions of $n!+1=m^2$ with $166906474 \le n < 175179856$ (Berndt-Galway search, group 21 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$166906474 \le n < 175179856.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 21 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 9 of 12 of block 1, `Brocard.berndt_galway_block_1`); it is proved from its 46 consecutive chunks (chunks 929 to 974 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_1`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_021 (n m : ℕ) (h1 : 166906474 ≤ n) (h2 : n < 175179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
