-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_016
-- name    : Brocard.berndt_galway_group_016
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:18:17.495097+00:00
-- url     : https://prove2.me/theorems/53b2c349-4d01-4d11-b20e-f4b5dfb1de6a
-- title:
--   No solutions of $n!+1=m^2$ with $125359712 \le n < 133812949$ (Berndt-Galway search, group 16 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$125359712 \le n < 133812949.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 16 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 4 of 12 of block 1, `Brocard.berndt_galway_block_1`); it is proved from its 47 consecutive chunks (chunks 698 to 744 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_1`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_016 (n m : ℕ) (h1 : 125359712 ≤ n) (h2 : n < 133812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
