-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_025
-- name    : Brocard.berndt_galway_group_025
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:08:57.066796+00:00
-- url     : https://prove2.me/theorems/b361ebc4-2f31-4330-9fe4-daa0bb9ab5f2
-- title:
--   No solutions of $n!+1=m^2$ with $200000000 \le n < 208453237$ (Berndt-Galway search, group 25 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$200000000 \le n < 208453237.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 25 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 1 of 12 of block 2, `Brocard.berndt_galway_block_2`); it is proved from its 47 consecutive chunks (chunks 1113 to 1159 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_2`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_025 (n m : ℕ) (h1 : 200000000 ≤ n) (h2 : n < 208453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
