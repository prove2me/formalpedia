-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_031
-- name    : Brocard.berndt_galway_group_031
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:33:27.287903+00:00
-- url     : https://prove2.me/theorems/fb0609ae-1858-4052-bcd8-0a567352fdea
-- title:
--   No solutions of $n!+1=m^2$ with $250359712 \le n < 258633093$ (Berndt-Galway search, group 31 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$250359712 \le n < 258633093.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 31 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 7 of 12 of block 2, `Brocard.berndt_galway_block_2`); it is proved from its 46 consecutive chunks (chunks 1393 to 1438 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_2`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_031 (n m : ℕ) (h1 : 250359712 ≤ n) (h2 : n < 258633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
