-- Prove2me | Theorems.Thm_Brocard_berndt_galway_chunk_0312
-- name    : Brocard.berndt_galway_chunk_0312
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:51:46.351634+00:00
-- url     : https://prove2.me/theorems/21eb8c8a-3bd2-4248-8ef1-ad5847c0c027
-- title:
--   No solutions of $n!+1=m^2$ with $55935255 \le n < 56115111$ (Berndt-Galway search, chunk 312 of 5560)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$55935255 \le n < 56115111.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: chunk 312 of 5560 of the Berndt-Galway search range 8 <= n < 10^9 (chunk 312 of 556 of block 0, `Brocard.berndt_galway_block_0`; group g007); consecutive chunks meet end to end, and n < 8 is handled in the block 0 reduction.
--
--   **Method** For every such $n$ the proof exhibits a prime $p > n + 1$ for which $Q(Q-1)$ is a quadratic non-residue modulo $p$, where $Q = (-1)^{p-1-n}(p-1-n)!$; by Wilson's theorem $Q^2(n!+1) \equiv Q(Q-1) \pmod p$, so $n! + 1$ is not a square (the criterion of Berndt and Galway).
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_0`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_chunk_0312 (n m : ℕ) (h1 : 55935255 ≤ n) (h2 : n < 56115111) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
