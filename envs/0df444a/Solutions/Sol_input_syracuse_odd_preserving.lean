-- Prove2me | solution 1 for input_syracuse_odd_preserving
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-29T01:14:53.426547+00:00
-- url     : https://prove2.me/submissions/61ab0b9e-cebf-4fbc-866d-21637604762a

import Mathlib
import Definitions.Def_syracuseOrbitMin

noncomputable section

attribute [instance] Classical.propDecidable

/-- Tao 2022, §1.2: the Syracuse map preserves oddness.
    For odd `n`, `Syr(n) = (3n+1)/2^ν₂(3n+1)`; writing `3n+1 = 2^e·m`
    with `m` odd (Mathlib: `Nat.exists_eq_two_pow_mul_odd`), the
    2-adic valuation is exactly `e`, so the quotient is the odd `m`. -/
theorem solution : ∀ n : ℕ, Odd n → Odd (syracuseStep n) := by
  intro n hn
  -- Definitional unfolding of the Syracuse step (server bundle).
  have hstep : syracuseStep n = (3 * n + 1) / 2 ^ Nat.factorization (3 * n + 1) 2 := rfl
  rw [hstep]
  obtain ⟨k, rfl⟩ := hn
  have hm_ne : 3 * (2 * k + 1) + 1 ≠ 0 := by omega
  obtain ⟨e, m, hmodd, hmeq⟩ := Nat.exists_eq_two_pow_mul_odd hm_ne
  -- The 2-adic valuation of `2^e * m` (with `m` odd) is `e`.
  have hfact : Nat.factorization (2 ^ e * m) 2 = e := by
    have h2e : (2 : ℕ) ^ e ≠ 0 := by positivity
    have hm0 : m ≠ 0 := by
      intro h
      rw [h, mul_zero] at hmeq
      omega
    have hnotdvd : ¬ (2 : ℕ) ∣ m := by
      intro hdvd
      exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hdvd)
    rw [Nat.factorization_mul h2e hm0, Finsupp.add_apply,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd hnotdvd, add_zero]
  rw [hmeq, hfact, Nat.mul_div_cancel_left m (by positivity : (0 : ℕ) < 2 ^ e)]
  exact hmodd

/-- Alias under the published node name (the platform verifier looks up
    `input_syracuse_odd_preserving`; `solution` above carries the proof). -/
theorem input_syracuse_odd_preserving : ∀ n : ℕ, Odd n → Odd (syracuseStep n) :=
  solution
