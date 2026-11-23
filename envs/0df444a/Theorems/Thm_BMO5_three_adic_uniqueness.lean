-- Prove2me | Theorems.Thm_BMO5_three_adic_uniqueness
-- name    : BMO5.three_adic_uniqueness
-- status  : Proved
-- author  : @alon yuval
-- created : 2026-11-23T16:48:48.466743+00:00
-- url     : https://prove2.me/theorems/348653bc-1e3e-412d-9107-b6a719b7a91e
-- title:
--   BMO #5: halting levels with $k$ triplings lie in one class mod $3^k$ per parity
-- statement:
--   Let $g(i) = 20\cdot 2^i + i + 1$. **Theorem.** If $i \equiv j \pmod 2$ and $3^k$ divides both $g(i)$ and $g(j)$, then $i \equiv j \pmod{3^k}$.
--
--   Context: in Beaver Math Olympiad problem 5, halting at level $i$ after $k$ tripling steps forces $3^k \mid g(i)$ (`BMO5.level_halt_dvd`). Hence, for each parity, all such levels lie in a single residue class modulo $3^k$, and these classes converge to two $3$-adic integers (one per parity). Existence of a class for each parity follows by Hensel-type lifting, because $4^{3^{k-1}} \equiv 1 \pmod{3^k}$ and $g(i + 2\cdot 3^{k-1}t) \equiv g(i) + 2\cdot 3^{k-1}t \pmod{3^k}$. So exactly two classes modulo $2\cdot 3^k$ admit halting after $k$ triplings, a set of density $3^{-k}$.
-- source:
--   Beaver Math Olympiad problem 5, https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad (machine 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE). Follow-up to BMO5.level_halt_dvd; original observation of this submission.

import Mathlib

namespace BMO5
theorem three_adic_uniqueness (k i j : ℕ) (hpar : i % 2 = j % 2)
    (hi : 3 ^ k ∣ 20 * 2 ^ i + i + 1) (hj : 3 ^ k ∣ 20 * 2 ^ j + j + 1) :
    i % 3 ^ k = j % 3 ^ k := by
  sorry
end BMO5
