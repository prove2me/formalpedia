-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_030
-- name    : Brocard.berndt_galway_group_030
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:13:52.633407+00:00
-- url     : https://prove2.me/theorems/c0b47943-5aeb-4d32-bd79-13e74770c62c
-- title:
--   No solutions of $n!+1=m^2$ with $242086330 \le n < 250359712$ (Berndt-Galway search, group 30 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$242086330 \le n < 250359712.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 30 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 6 of 12 of block 2, `Brocard.berndt_galway_block_2`); it is proved from its 46 consecutive chunks (chunks 1347 to 1392 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_2`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_030 (n m : ℕ) (h1 : 242086330 ≤ n) (h2 : n < 250359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
