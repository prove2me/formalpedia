-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_095
-- name    : Brocard.berndt_galway_group_095
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:20:17.569213+00:00
-- url     : https://prove2.me/theorems/ae7e920f-2fb8-4d30-9f50-e6fc5a6421be
-- title:
--   No solutions of $n!+1=m^2$ with $783453237 \le n < 791726618$ (Berndt-Galway search, group 95 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$783453237 \le n < 791726618.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 95 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 11 of 12 of block 7, `Brocard.berndt_galway_block_7`); it is proved from its 46 consecutive chunks (chunks 4357 to 4402 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_7`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_095 (n m : ℕ) (h1 : 783453237 ≤ n) (h2 : n < 791726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
