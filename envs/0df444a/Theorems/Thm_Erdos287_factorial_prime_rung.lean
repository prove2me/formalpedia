-- Prove2me | Theorems.Thm_Erdos287_factorial_prime_rung
-- name    : Erdos287.factorial_prime_rung
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T05:06:10.946979+00:00
-- url     : https://prove2.me/theorems/bb032568-5c30-467d-ab40-636005c17309
-- title:
--   Adjacent prime multiples with factorial cofactor bounds exclude a band of maxima
-- statement:
--   A consecutive pair x,x+1 with prime divisors p,q excludes a band of possible maxima in an Egyptian fraction representation of 1, provided the two cofactor factorial bounds and the displayed endpoint inequalities hold.
-- source:
--   Erdős Problem #287; the factorial rung in the public P287.StepA2 development by Zed-Rez, adapted to the Prove2me formulation.

import Mathlib

theorem Erdos287.factorial_prime_rung (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (x p q B D : ℕ) (hp : p.Prime) (hq : q.Prime) (hdivp : p ∣ x) (hdivq : q ∣ x + 1)
    (hfp : B * B.factorial < p) (hfq : D * D.factorial < q)
    (hlo : x + 2 ≤ f (k - 1))
    (hhip : f (k - 1) < (B + 1) * p) (hhiq : f (k - 1) < (D + 1) * q)
    (hband : 2 * f (k - 1) + 20 ≤ 5 * x) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by sorry
