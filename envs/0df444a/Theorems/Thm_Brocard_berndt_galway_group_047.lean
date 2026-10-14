-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_047
-- name    : Brocard.berndt_galway_group_047
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:42:10.429505+00:00
-- url     : https://prove2.me/theorems/e660a408-c094-491d-a5f3-43559e43114b
-- title:
--   No solutions of $n!+1=m^2$ with $383453237 \le n < 391726618$ (Berndt-Galway search, group 47 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$383453237 \le n < 391726618.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 47 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 11 of 12 of block 3, `Brocard.berndt_galway_block_3`); it is proved from its 46 consecutive chunks (chunks 2133 to 2178 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_3`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_047 (n m : ℕ) (h1 : 383453237 ≤ n) (h2 : n < 391726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
