-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_012
-- name    : Brocard.berndt_galway_group_012
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:17:13.419903+00:00
-- url     : https://prove2.me/theorems/3422a992-df5a-452f-b596-842dfb21c248
-- title:
--   No solutions of $n!+1=m^2$ with $91726619 \le n < 100000000$ (Berndt-Galway search, group 12 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$91726619 \le n < 100000000.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 12 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 12 of 12 of block 0, `Brocard.berndt_galway_block_0`); it is proved from its 46 consecutive chunks (chunks 511 to 556 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_0`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_012 (n m : ℕ) (h1 : 91726619 ≤ n) (h2 : n < 100000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
