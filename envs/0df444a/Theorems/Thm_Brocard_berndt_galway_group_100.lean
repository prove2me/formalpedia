-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_100
-- name    : Brocard.berndt_galway_group_100
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:02:33.804001+00:00
-- url     : https://prove2.me/theorems/5851fd08-5bb6-4c71-9efe-7b9d402772b8
-- title:
--   No solutions of $n!+1=m^2$ with $825359712 \le n < 833812949$ (Berndt-Galway search, group 100 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$825359712 \le n < 833812949.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 100 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 4 of 12 of block 8, `Brocard.berndt_galway_block_8`); it is proved from its 47 consecutive chunks (chunks 4590 to 4636 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_8`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_100 (n m : ℕ) (h1 : 825359712 ≤ n) (h2 : n < 833812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
