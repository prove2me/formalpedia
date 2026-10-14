-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_020
-- name    : Brocard.berndt_galway_group_020
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:09:52.916517+00:00
-- url     : https://prove2.me/theorems/50bbd753-b950-48fb-b08b-3d700106e9c2
-- title:
--   No solutions of $n!+1=m^2$ with $158633093 \le n < 166906474$ (Berndt-Galway search, group 20 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$158633093 \le n < 166906474.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 20 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 8 of 12 of block 1, `Brocard.berndt_galway_block_1`); it is proved from its 46 consecutive chunks (chunks 883 to 928 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_1`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_020 (n m : ℕ) (h1 : 158633093 ≤ n) (h2 : n < 166906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
