-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_023
-- name    : Brocard.berndt_galway_group_023
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:33:40.123481+00:00
-- url     : https://prove2.me/theorems/408393ff-bf68-4518-ae4f-02b82013a923
-- title:
--   No solutions of $n!+1=m^2$ with $183453237 \le n < 191726618$ (Berndt-Galway search, group 23 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$183453237 \le n < 191726618.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 23 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 11 of 12 of block 1, `Brocard.berndt_galway_block_1`); it is proved from its 46 consecutive chunks (chunks 1021 to 1066 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_1`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_023 (n m : ℕ) (h1 : 183453237 ≤ n) (h2 : n < 191726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
