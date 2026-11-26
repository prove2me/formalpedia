-- Prove2me | Theorems.Thm_Erdos287_reconstruct_unit_sum_at_carry_prime
-- name    : Erdos287.reconstruct_unit_sum_at_carry_prime
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T14:41:03.213806+00:00
-- url     : https://prove2.me/theorems/df4f0ca0-c8a1-4220-afd7-f1ac4aab5e0e
-- title:
--   Reconstructing a unit sum by extra precision at a carry prime
-- statement:
--   Let $L>0$, $p$ be prime, $G=\gcd(L,C)$ and $K=L/G$. If $|W/L-1|G<p^j$, then $W/L=1$ if and only if its reduced denominator divides $C$ and $p^{v_p(K)+j}$ divides $|W-L|$. The prime may also divide $L$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.reconstruct_unit_sum_at_carry_prime (W L C p j : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hbound : |(W : ℚ) / L - 1| * (L.gcd C : ℚ) < (p ^ j : ℕ)) :
    (W : ℚ) / L = 1 ↔
      ((W : ℚ) / L).den ∣ C ∧
        p ^ ((L / L.gcd C).factorization p + j) ∣ Int.natAbs ((W : ℤ) - L) := by sorry
