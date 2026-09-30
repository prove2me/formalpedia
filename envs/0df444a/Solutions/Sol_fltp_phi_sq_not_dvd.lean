-- Prove2me | solution 1 for fltp_phi_sq_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:37:59.231326+00:00
-- url     : https://prove2.me/submissions/ee796720-35fd-4afc-b8c8-3d36d6412762

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset in
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    ¬(p : ℤ) ^ 2 ∣ ∑ i ∈ range p, a ^ i * (-b) ^ (p - 1 - i) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hxy : (p : ℤ) ∣ a - (-b) := by simpa [sub_neg_eq_add] using h_dvd
  -- Lifting the exponent: the `p`-adic valuation of `Φ_p(a, -b)` is exactly `1`.
  have h1 := emultiplicity_geom_sum₂_eq_one hp' h_odd hxy h_ndvd
  intro hdiv
  have h2 := pow_dvd_iff_le_emultiplicity.mp hdiv
  rw [h1] at h2
  have h3 : (2 : ℕ) ≤ 1 := by exact_mod_cast h2
  omega
