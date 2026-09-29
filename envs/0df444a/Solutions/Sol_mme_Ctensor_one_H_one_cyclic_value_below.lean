-- Prove2me | solution 1 for mme_Ctensor_one_H_one_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:19:04.948329+00:00
-- url     : https://prove2.me/submissions/ed99da75-b70e-4bd7-b271-ef4f6be16a84

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_Ctensor_one_H_one_balanced_extractions_sqrt_loss
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (H : ℝ) ^ 2 * (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (cyclicSymmetrization T) tau V := by
  let B : ℝ :=
    (H : ℝ) ^ 2 * (((volume ^ 3 : ℕ) : ℝ) ^ tau)
  have hVB : V < B := by simpa [B] using hVlt
  have hH : 0 < H := by
    by_contra h
    have hzero : H = 0 := Nat.eq_zero_of_not_pos h
    subst H
    simp at hVlt
    linarith
  have htau_pos : 0 < tau := by linarith
  have hvolume : 0 < volume := by
    by_contra h
    have hzero : volume = 0 := Nat.eq_zero_of_not_pos h
    subst volume
    simp [Real.zero_rpow htau_pos.ne'] at hVlt
    linarith
  obtain ⟨C, hC, hfinite⟩ :=
    mme_Ctensor_one_H_one_balanced_extractions_sqrt_loss
      cert hH hvolume tau htau
  let s : ℕ → ℕ := fun m => H * m
  have hs : Tendsto s atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    dsimp [s]
    exact hm.trans (by
      simpa [mul_comm] using Nat.le_mul_of_pos_right m hH)
  have hgap0 :=
    mme_strict_pow_absorbs_sqrt_exp_loss V B C hV hVB hC
  have hgap :
      ∀ᶠ m : ℕ in atTop,
        V ^ (s m) ≤ B ^ (s m) *
          Real.exp
            (-C * Real.sqrt ((((s m) + 1 : ℕ) : ℝ))) :=
    hs.eventually hgap0
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (T := cyclicSymmetrization T) tau V hV s hs
    (fun _ => (0 : ℝ)) tendsto_const_nhds
  filter_upwards [hfinite, hgap] with m hm hmgap
  dsimp only at hm
  obtain ⟨k, a, b, c, hrestrict, hcount⟩ := hm
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simp only [sub_zero, mul_one]
  exact hmgap.trans (by
    change B ^ (s m) *
        Real.exp
          (-C * Real.sqrt ((((s m) + 1 : ℕ) : ℝ))) ≤
      ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)
    simpa [B, s] using hcount)
