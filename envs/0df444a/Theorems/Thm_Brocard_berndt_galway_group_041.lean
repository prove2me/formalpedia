-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_041
-- name    : Brocard.berndt_galway_group_041
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:49:17.101048+00:00
-- url     : https://prove2.me/theorems/0596bea1-02ab-4988-b294-e69ee3474069
-- title:
--   No solutions of $n!+1=m^2$ with $333812949 \le n < 342086330$ (Berndt-Galway search, group 41 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$333812949 \le n < 342086330.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 41 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 5 of 12 of block 3, `Brocard.berndt_galway_block_3`); it is proved from its 46 consecutive chunks (chunks 1857 to 1902 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_3`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_041 (n m : ℕ) (h1 : 333812949 ≤ n) (h2 : n < 342086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
