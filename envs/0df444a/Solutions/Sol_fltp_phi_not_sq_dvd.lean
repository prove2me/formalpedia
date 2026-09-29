-- Prove2me | solution 1 for fltp_phi_not_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T11:07:52.781656+00:00
-- url     : https://prove2.me/submissions/2e51f316-8a3d-49e3-aa08-0fb71ae8a3dc

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    ¬(p : ℤ) ^ 2 ∣ ∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i) := by
  have h_ndvd_b : ¬(p : ℤ) ∣ b := by
    intro hdvdb
    apply h_ndvd
    obtain ⟨k, hk⟩ := h_dvd; obtain ⟨m, hm⟩ := hdvdb
    exact ⟨k - m, by linarith⟩
  obtain ⟨k, hk⟩ := h_dvd
  have ha_eq : a = -b + (p : ℤ) * k := by linarith
  have hmod : (p : ℤ) ^ 2 ∣
      (∑ i ∈ Finset.range p, (-b + (p : ℤ) * k) ^ i * (-b) ^ (p - 1 - i)) -
      (p : ℤ) * (-b) ^ (p - 1) :=
    odd_sq_dvd_geom_sum₂_sub (-b) k h_odd
  rw [ha_eq.symm] at hmod
  intro h2dvd
  have h_sq_dvd_pb : (p : ℤ) ^ 2 ∣ (p : ℤ) * (-b) ^ (p - 1) := by
    obtain ⟨s, hs⟩ := h2dvd; obtain ⟨t, ht⟩ := hmod
    exact ⟨s - t, by linarith⟩
  have h_p_dvd_pow : (p : ℤ) ∣ (-b) ^ (p - 1) := by
    rw [sq, mul_dvd_mul_iff_left (by exact_mod_cast hp.out.pos.ne')] at h_sq_dvd_pb
    exact h_sq_dvd_pb
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  exact h_ndvd_b ((dvd_neg.mp (hp'.dvd_of_dvd_pow h_p_dvd_pow)))
