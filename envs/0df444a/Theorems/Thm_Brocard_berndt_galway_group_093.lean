-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_093
-- name    : Brocard.berndt_galway_group_093
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:00:53.017465+00:00
-- url     : https://prove2.me/theorems/2896da5c-9e80-47a7-94ba-667996ff7d95
-- title:
--   No solutions of $n!+1=m^2$ with $766906474 \le n < 775179856$ (Berndt-Galway search, group 93 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$766906474 \le n < 775179856.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 93 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 9 of 12 of block 7, `Brocard.berndt_galway_block_7`); it is proved from its 46 consecutive chunks (chunks 4265 to 4310 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_7`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_093 (n m : ℕ) (h1 : 766906474 ≤ n) (h2 : n < 775179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
