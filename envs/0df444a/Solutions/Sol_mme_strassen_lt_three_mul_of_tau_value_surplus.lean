-- Prove2me | solution 1 for mme_strassen_lt_three_mul_of_tau_value_surplus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:54:23.93002+00:00
-- url     : https://prove2.me/submissions/a172d88a-03b3-411f-bb8a-a186d96bc34c

import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_tau_value_le_of_asymptoticRank_le

open MME BigOperators Filter

universe u

private theorem hasTauValueAtLeast_mono_tau
    {K : Type u} [Field K] {T : TensorObj K 3} {tau tau' V : ℝ}
    (htau : 0 < tau) (htau' : tau ≤ tau')
    (hV : HasTauValueAtLeast T tau V) :
    HasTauValueAtLeast T tau' V := by
  refine ⟨hV.1, ?_⟩
  intro epsilon hepsilon
  exact (hV.2 epsilon hepsilon).mono (fun N hN => by
    rcases hN with ⟨k, a, b, c, hrestrict, hweight⟩
    refine ⟨k, a, b, c, hrestrict, hweight.trans ?_⟩
    apply Finset.sum_le_sum
    intro i hi
    by_cases hzero : a i * b i * c i = 0
    · simp only [hzero, Nat.cast_zero]
      rw [Real.zero_rpow htau.ne', Real.zero_rpow (htau.trans_le htau').ne']
    · exact Real.rpow_le_rpow_of_exponent_le
        (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hzero)) htau')

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {tau V R : ℝ}
    (htau : 0 < tau) (hV_one : 1 ≤ V) (hR_nonneg : 0 ≤ R)
    (hR : tensorAsymptoticRank T ≤ R)
    (hV : HasTauValueAtLeast T tau V)
    (hsurplus : R < V) :
    matMulExp_strassen K < 3 * tau := by
  have hexponent : matMulExp_strassen K / 3 < tau := by
    by_contra hnot
    have htau_le : tau ≤ matMulExp_strassen K / 3 := le_of_not_gt hnot
    have hV_at_omega :
        HasTauValueAtLeast T (matMulExp_strassen K / 3) V :=
      hasTauValueAtLeast_mono_tau htau htau_le hV
    have hV_le_R := mme_tau_value_le_of_asymptoticRank_le
      hR_nonneg hV_one hR hV_at_omega
    exact (not_lt_of_ge hV_le_R) hsurplus
  linarith
