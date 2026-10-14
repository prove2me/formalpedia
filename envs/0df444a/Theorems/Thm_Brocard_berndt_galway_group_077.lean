-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_077
-- name    : Brocard.berndt_galway_group_077
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:51:00.465997+00:00
-- url     : https://prove2.me/theorems/4f6e897f-d70d-4648-a4b1-57f596f250d3
-- title:
--   No solutions of $n!+1=m^2$ with $633812949 \le n < 642086330$ (Berndt-Galway search, group 77 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$633812949 \le n < 642086330.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 77 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 5 of 12 of block 6, `Brocard.berndt_galway_block_6`); it is proved from its 46 consecutive chunks (chunks 3525 to 3570 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_6`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_077 (n m : ℕ) (h1 : 633812949 ≤ n) (h2 : n < 642086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
