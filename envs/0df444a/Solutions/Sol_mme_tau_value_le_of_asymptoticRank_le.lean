-- Prove2me | solution 1 for mme_tau_value_le_of_asymptoticRank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:29:53.346799+00:00
-- url     : https://prove2.me/submissions/a3c43461-05a4-47ab-9862-530bf49b1ce1

import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_asymptotic_sum_inequality_sharp
import Theorems.Thm_mme_tensorAsymptoticRank_mono_restrict
import Theorems.Thm_mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
import Theorems.Thm_mme_le_of_frequently_pow_half_le

open MME BigOperators Filter

universe u

private lemma tensorAsymptoticRank_nonneg
    {K : Type u} [Field K] {d : ℕ} (T : TensorObj K d) :
    0 ≤ tensorAsymptoticRank T := by
  unfold tensorAsymptoticRank
  change (0 : ℝ) ≤ ⨅ n : ℕ,
    (tensorRankObj (T.kronPow (n + 1)) : ℝ) ^ ((1 : ℝ) / (n + 1))
  apply le_ciInf
  intro n
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {R V : ℝ}
    (hR_nonneg : 0 ≤ R) (hV_one : 1 ≤ V)
    (hR : tensorAsymptoticRank T ≤ R)
    (hV : HasTauValueAtLeast T (matMulExp_strassen K / 3) V) :
    V ≤ R := by
  apply mme_le_of_frequently_pow_half_le hV_one hR_nonneg
  have hwitness := hV.2 (1 / 2) (by norm_num)
  have hlarge : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  refine (hwitness.and_eventually hlarge).mono ?_
  rintro N ⟨⟨k, a, b, c, hrestrict, hweight⟩, hN⟩
  have hAR_nonneg : 0 ≤ tensorAsymptoticRank T :=
    tensorAsymptoticRank_nonneg T
  calc
    V ^ N * (1 / 2 : ℝ) = V ^ N * (1 - (1 / 2 : ℝ)) := by ring
    _ ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^
          (matMulExp_strassen K / 3)) := hweight
    _ ≤ tensorAsymptoticRank
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i))) :=
      mme_asymptotic_sum_inequality_sharp a b c
    _ ≤ tensorAsymptoticRank (T.kronPow N) :=
      mme_tensorAsymptoticRank_mono_restrict hrestrict
    _ = tensorAsymptoticRank T ^ N :=
      mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
        (K := K) (by norm_num) T N hN
    _ ≤ R ^ N := pow_le_pow_left₀ hAR_nonneg hR N
