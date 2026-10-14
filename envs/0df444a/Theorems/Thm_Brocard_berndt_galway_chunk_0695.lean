-- Prove2me | Theorems.Thm_Brocard_berndt_galway_chunk_0695
-- name    : Brocard.berndt_galway_chunk_0695
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:59:47.959449+00:00
-- url     : https://prove2.me/theorems/3d8fd611-8bad-482e-9b13-886186f2946a
-- title:
--   No solutions of $n!+1=m^2$ with $124820143 \le n < 125000000$ (Berndt-Galway search, chunk 695 of 5560)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$124820143 \le n < 125000000.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: chunk 695 of 5560 of the Berndt-Galway search range 8 <= n < 10^9 (chunk 139 of 556 of block 1, `Brocard.berndt_galway_block_1`; group g015); consecutive chunks meet end to end, and n < 8 is handled in the block 0 reduction.
--
--   **Method** For every such $n$ the proof exhibits a prime $p > n + 1$ for which $Q(Q-1)$ is a quadratic non-residue modulo $p$, where $Q = (-1)^{p-1-n}(p-1-n)!$; by Wilson's theorem $Q^2(n!+1) \equiv Q(Q-1) \pmod p$, so $n! + 1$ is not a square (the criterion of Berndt and Galway).
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_1`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_chunk_0695 (n m : ℕ) (h1 : 124820143 ≤ n) (h2 : n < 125000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
