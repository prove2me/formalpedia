-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_013
-- name    : Brocard.berndt_galway_group_013
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:33:04.59478+00:00
-- url     : https://prove2.me/theorems/6586c1e6-6338-4f68-a91c-7b6914af4895
-- title:
--   No solutions of $n!+1=m^2$ with $100000000 \le n < 108453237$ (Berndt-Galway search, group 13 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$100000000 \le n < 108453237.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 13 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 1 of 12 of block 1, `Brocard.berndt_galway_block_1`); it is proved from its 47 consecutive chunks (chunks 557 to 603 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_1`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_013 (n m : ℕ) (h1 : 100000000 ≤ n) (h2 : n < 108453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
