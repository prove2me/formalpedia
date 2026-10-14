-- Prove2me | Theorems.Thm_Brocard_berndt_galway_group_046
-- name    : Brocard.berndt_galway_group_046
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:33:22.091617+00:00
-- url     : https://prove2.me/theorems/f31b7619-cb25-4029-95bf-69aa4fd369ee
-- title:
--   No solutions of $n!+1=m^2$ with $375179856 \le n < 383453237$ (Berndt-Galway search, group 46 of 120)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$375179856 \le n < 383453237.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: group 46 of 120 of the Berndt-Galway search range 8 <= n < 10^9 (group 10 of 12 of block 3, `Brocard.berndt_galway_block_3`); it is proved from its 46 consecutive chunks (chunks 2087 to 2132 of 5560), and the groups meet end to end.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_3`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_group_046 (n m : ℕ) (h1 : 375179856 ≤ n) (h2 : n < 383453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
