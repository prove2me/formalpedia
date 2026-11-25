-- Prove2me | solution 1 for witt_logarithm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:22:29.068373+00:00
-- url     : https://prove2.me/submissions/a621f472-3b11-4cba-b87e-2427ac74943e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_InvSerSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_WfLogOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittLogarithm
import Theorems.Thm_PI_WfLogWork_formal_logarithm_holds
import Theorems.Thm_PI_WfLogWork_wfLog_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private lemma inv_series_sub : PI.InvSerSub := by
  intro K _ S l ex hl hl0 hl1 hex0 hsub n
  obtain ⟨c, hc⟩ := PowerSeries.X_dvd_iff.2 hex0
  have hpow : ∀ d m, PowerSeries.coeff m (ex ^ d) =
      if d ≤ m then PowerSeries.coeff (m - d) (c ^ d) else 0 := by
    intro d m
    rw [hc, mul_pow, PowerSeries.coeff_X_pow_mul']
  have hcoef : ∀ j, PowerSeries.coeff j c = PowerSeries.coeff (j + 1) ex := by
    intro j
    rw [hc, PowerSeries.coeff_succ_X_mul]
  have hHS : PowerSeries.HasSubst ex := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [hex0]; exact IsNilpotent.zero)
  have key : ∀ m, PowerSeries.coeff m (PowerSeries.X : PowerSeries K) =
      ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l * PowerSeries.coeff m (ex ^ d) := by
    intro m
    have hfin : (∑ᶠ d, PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d)) =
        ∑ d ∈ Finset.range (m + 1), PowerSeries.coeff d l • PowerSeries.coeff m (ex ^ d) := by
      apply finsum_eq_sum_of_support_subset
      intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [hpow, if_neg (by omega), smul_zero]
    rw [← hsub, PowerSeries.coeff_subst' hHS, hfin]
    simp only [smul_eq_mul]

  have hB : ∀ N, (∀ j ≤ N, PowerSeries.coeff j c ∈ S) →
      ∀ d, ∀ i ≤ N, PowerSeries.coeff i (c ^ d) ∈ S := by
    intro N hN d
    induction d with
    | zero =>
      intro i _
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    | succ d ihd =>
      intro i hi
      rw [pow_succ, PowerSeries.coeff_mul]
      apply Subring.sum_mem
      intro p hp
      have h : p.1 + p.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      exact S.mul_mem (ihd _ (by omega)) (hN _ (by omega))
  have hl0' : PowerSeries.coeff 0 l = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hex0]
      exact S.zero_mem
    · have k := key (n + 1)
      rw [Finset.sum_range_succ', Finset.sum_range_succ'] at k
      simp only [zero_add, pow_one, hl1, one_mul, hl0', zero_mul, add_zero] at k
      have he : PowerSeries.coeff (n + 1) ex = PowerSeries.coeff (n + 1) (PowerSeries.X : PowerSeries K) -
          ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1 + 1) l *
            PowerSeries.coeff (n + 1) (ex ^ (i + 1 + 1)) := by
        rw [k]
        ring
      rw [he]
      apply S.sub_mem
      · rw [PowerSeries.coeff_X]
        split_ifs
        · exact S.one_mem
        · exact S.zero_mem
      · apply Subring.sum_mem
        intro i hi
        rw [Finset.mem_range] at hi
        apply S.mul_mem (hl _)
        rw [hpow]
        split_ifs with hle
        · apply hB (n - 1) _ (i + 1 + 1) _ (by omega)
          intro j hj
          rw [hcoef]
          exact ih _ (by omega)
        · exact S.zero_mem
end

set_option autoImplicit false

theorem _root_.solution : PI.WfLog :=
  PI.WfLogWork.wfLog_of inv_series_sub PI.WfLogWork.formal_logarithm_holds
