-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_050
-- name    : Brocard.berndt_galway_group_050
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:08:58.96197+00:00
-- url     : https://prove2.me/theorems/7ac78510-c28f-4aeb-9af0-afc733081c68
-- title:
--   No solutions of $n!+1=m^2$ with $408453237 \le n < 416906474$ (Berndt-Galway search, group 50 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$408453237 \le n < 416906474.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 50 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 2 of 12 of block 4, `Brocard.berndt_galway_block_4`); it is proved from its 47 consecutive chunks (chunks 2272 to 2318 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_4`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_050 (n m : ℕ) (h1 : 408453237 ≤ n) (h2 : n < 416906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
