-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_008
-- name    : Brocard.berndt_galway_group_008
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:13:48.973759+00:00
-- url     : https://prove2.me/theorems/a0b86a84-1100-4ba3-b80d-4aaa6267f9f8
-- title:
--   No solutions of $n!+1=m^2$ with $58633096 \le n < 66906477$ (Berndt-Galway search, group 8 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$58633096 \le n < 66906477.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 8 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 8 of 12 of block 0, `Brocard.berndt_galway_block_0`); it is proved from its 46 consecutive chunks (chunks 327 to 372 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_0`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_008 (n m : ℕ) (h1 : 58633096 ≤ n) (h2 : n < 66906477) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
