-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_085
-- name    : Brocard.berndt_galway_group_085
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:29.667813+00:00
-- url     : https://prove2.me/theorems/a77da23b-ad39-470b-a057-3c0165f4a620
-- title:
--   No solutions of $n!+1=m^2$ with $700000000 \le n < 708453237$ (Berndt-Galway search, group 85 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$700000000 \le n < 708453237.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 85 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 1 of 12 of block 7, `Brocard.berndt_galway_block_7`); it is proved from its 47 consecutive chunks (chunks 3893 to 3939 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_7`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_085 (n m : ℕ) (h1 : 700000000 ≤ n) (h2 : n < 708453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
