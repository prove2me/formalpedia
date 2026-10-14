-- Prove2me | Theorems.Thm_Brocard_berndt_galway_chunk_2522
-- name    : Brocard.berndt_galway_chunk_2522
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:45:23.661007+00:00
-- url     : https://prove2.me/theorems/0e13ccc9-4fcf-4564-8a54-e86135c6fcf3
-- title:
--   No solutions of $n!+1=m^2$ with $453417266 \le n < 453597122$ (Berndt-Galway search, chunk 2522 of 5560)
-- statement:
--   Let $n$ and $m$ be natural numbers with
--   $$453417266 \le n < 453597122.$$
--   Then $n! + 1 \neq m^2$; that is, Brocard's equation has no solution with $n$ in this range.
--
--   Role: chunk 2522 of 5560 of the Berndt-Galway search range 8 <= n < 10^9 (chunk 298 of 556 of block 4, `Brocard.berndt_galway_block_4`; group g055); consecutive chunks meet end to end, and n < 8 is handled in the block 0 reduction.
--
--   **Method** For every such $n$ the proof exhibits a prime $p > n + 1$ for which $Q(Q-1)$ is a quadratic non-residue modulo $p$, where $Q = (-1)^{p-1-n}(p-1-n)!$; by Wilson's theorem $Q^2(n!+1) \equiv Q(Q-1) \pmod p$, so $n! + 1$ is not a square (the criterion of Berndt and Galway).
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard-Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), pp. 41-42, https://doi.org/10.1023/A:1009873805276 (the computer search for n < 10^9 with the quadratic non-residue criterion, proved here as `Brocard.berndt_galway_criterion`); finite verification of one sub-range of the block `Brocard.berndt_galway_block_4`.

import Mathlib.Data.Nat.Factorial.Basic

namespace Brocard

theorem berndt_galway_chunk_2522 (n m : ℕ) (h1 : 453417266 ≤ n) (h2 : n < 453597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by sorry

end Brocard
