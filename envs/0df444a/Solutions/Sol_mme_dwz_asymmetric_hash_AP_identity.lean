-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_AP_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:21:17.872648+00:00
-- url     : https://prove2.me/submissions/950cc0f5-5d64-4ae4-bccf-9ee85f3aad50

import Definitions.Def_mme_dwz_asymmetric_affine_hash

open BigOperators

set_option autoImplicit false
set_option warningAsError true

open MME

theorem solution
    {p N : ℕ} (hpodd : Odd p) (levelSum : ZMod p)
    (ω : DWZAsymmetricHashState p N)
    (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum) :
    dwzAsymmetricHashX ω I + dwzAsymmetricHashY ω J =
      2 * dwzAsymmetricHashZ levelSum ω K := by
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
  have htwo : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [mul_comm]
    exact ZMod.inv_mul_of_unit 2 hunit
  have hsum :
      (∑ t, I t * ω.weight t) + (∑ t, J t * ω.weight t) =
        ∑ t, (levelSum - K t) * ω.weight t := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    have ht := hsupport t
    have hij : I t + J t = levelSum - K t := by
      exact eq_sub_iff_add_eq.mpr ht
    rw [← add_mul, hij]
  simp only [dwzAsymmetricHashX, dwzAsymmetricHashY,
    dwzAsymmetricHashZ]
  rw [mul_add, ← mul_assoc, htwo, one_mul]
  rw [← hsum]
  ring
