-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_089
-- name    : Brocard.berndt_galway_group_089
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:43.296633+00:00
-- url     : https://prove2.me/theorems/bce76664-ec40-4b43-8bb4-99baaf25636f
-- title:
--   No solutions of $n!+1=m^2$ with $733812949 \le n < 742086330$ (Berndt-Galway search, group 89 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$733812949 \le n < 742086330.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 89 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 5 of 12 of block 7, `Brocard.berndt_galway_block_7`); it is proved from its 46 consecutive chunks (chunks 4081 to 4126 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_7`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_089 (n m : ℕ) (h1 : 733812949 ≤ n) (h2 : n < 742086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
