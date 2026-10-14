-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_022
-- name    : Brocard.berndt_galway_group_022
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:03:25.53363+00:00
-- url     : https://prove2.me/theorems/c93b8dd1-08c5-46d2-88e5-37a2cdca97b8
-- title:
--   No solutions of $n!+1=m^2$ with $175179856 \le n < 183453237$ (Berndt-Galway search, group 22 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$175179856 \le n < 183453237.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 22 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 10 of 12 of block 1, `Brocard.berndt_galway_block_1`); it is proved from its 46 consecutive chunks (chunks 975 to 1020 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_1`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_022 (n m : ℕ) (h1 : 175179856 ≤ n) (h2 : n < 183453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
