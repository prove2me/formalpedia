-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_006
-- name    : Brocard.berndt_galway_group_006
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:41:51.860844+00:00
-- url     : https://prove2.me/theorems/c5718f27-7f32-4214-b8f3-ff8cc66c16c0
-- title:
--   No solutions of $n!+1=m^2$ with $42086335 \le n < 50359716$ (Berndt-Galway search, group 6 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$42086335 \le n < 50359716.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 6 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 6 of 12 of block 0, `Brocard.berndt_galway_block_0`); it is proved from its 46 consecutive chunks (chunks 235 to 280 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_0`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_006 (n m : ℕ) (h1 : 42086335 ≤ n) (h2 : n < 50359716) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
