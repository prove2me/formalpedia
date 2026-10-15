-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_090
-- name    : Brocard.berndt_galway_group_090
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:37:20.091672+00:00
-- url     : https://prove2.me/theorems/ada1eaef-4ceb-4744-a9e8-5583e4da9c10
-- title:
--   No solutions of $n!+1=m^2$ with $742086330 \le n < 750359712$ (Berndt-Galway search, group 90 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$742086330 \le n < 750359712.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 90 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 6 of 12 of block 7, `Brocard.berndt_galway_block_7`); it is proved from its 46 consecutive chunks (chunks 4127 to 4172 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_7`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_090 (n m : ℕ) (h1 : 742086330 ≤ n) (h2 : n < 750359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
