-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_107
-- name    : Brocard.berndt_galway_group_107
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:08:06.324995+00:00
-- url     : https://prove2.me/theorems/bc6a1cff-aa79-47cb-9a32-8bea6402350d
-- title:
--   No solutions of $n!+1=m^2$ with $883453237 \le n < 891726618$ (Berndt-Galway search, group 107 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$883453237 \le n < 891726618.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 107 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 11 of 12 of block 8, `Brocard.berndt_galway_block_8`); it is proved from its 46 consecutive chunks (chunks 4913 to 4958 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_8`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_107 (n m : ℕ) (h1 : 883453237 ≤ n) (h2 : n < 891726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
