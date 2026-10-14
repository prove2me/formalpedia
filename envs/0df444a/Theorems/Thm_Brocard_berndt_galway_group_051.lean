-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_051
-- name    : Brocard.berndt_galway_group_051
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:18:59.644499+00:00
-- url     : https://prove2.me/theorems/89a93345-6a05-4c43-b1ea-0d9fcd633c04
-- title:
--   No solutions of $n!+1=m^2$ with $416906474 \le n < 425359712$ (Berndt-Galway search, group 51 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$416906474 \le n < 425359712.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 51 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 3 of 12 of block 4, `Brocard.berndt_galway_block_4`); it is proved from its 47 consecutive chunks (chunks 2319 to 2365 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_4`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_051 (n m : ℕ) (h1 : 416906474 ≤ n) (h2 : n < 425359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
