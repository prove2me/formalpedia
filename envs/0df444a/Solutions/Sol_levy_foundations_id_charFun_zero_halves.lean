-- Prove2me | solution 1 for levy_foundations_id_charFun_zero_halves
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:14:28.2202+00:00
-- url     : https://prove2.me/submissions/a238d864-e143-48b1-b1fb-07abc870beca

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_iteratedConvolutionPower
import Theorems.Thm_levy_foundations_charFun_iteratedConvolutionPower
import Theorems.Thm_levy_foundations_charFun_zero_double_half_norm_sq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem solution
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ)
    (ξ : ℝ)
    (hzero : charFun μ (2 * ξ) = 0) :
    charFun μ ξ = 0 := by
  have hconv (ν : Measure ℝ) (n : ℕ) :
      LevyFoundations.iteratedConvolutionPower ν n =
        LevyFoundations.iteratedConv ν n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        change ν ∗ LevyFoundations.iteratedConvolutionPower ν n =
          ν ∗ LevyFoundations.iteratedConv ν n
        rw [ih]
  have hevent :
      ∀ᶠ n : ℕ in atTop, ‖charFun μ ξ‖ ^ 2 ≤ (1 / 2 : ℝ) ^ n := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    obtain ⟨ν, hν, hroot⟩ := hμ n (by omega)
    letI : IsProbabilityMeasure ν := hν
    have hpowtwo :
        (charFun ν (2 * ξ)) ^ n = (0 : ℂ) := by
      calc
        _ = charFun (LevyFoundations.iteratedConvolutionPower ν n) (2 * ξ) :=
          (levy_foundations_charFun_iteratedConvolutionPower ν n (2 * ξ)).symm
        _ = charFun μ (2 * ξ) := by
          rw [hconv, ← hroot]
        _ = 0 := hzero
    have hνzero : charFun ν (2 * ξ) = 0 := by
      by_contra hne
      exact (pow_ne_zero n hne) hpowtwo
    have hbound : ‖charFun ν ξ‖ ^ 2 ≤ (1 / 2 : ℝ) :=
      levy_foundations_charFun_zero_double_half_norm_sq ν ξ hνzero
    have hrootξ : charFun μ ξ = (charFun ν ξ) ^ n := by
      calc
        _ = charFun (LevyFoundations.iteratedConvolutionPower ν n) ξ := by
          rw [hconv, ← hroot]
        _ = (charFun ν ξ) ^ n :=
          levy_foundations_charFun_iteratedConvolutionPower ν n ξ
    calc
      ‖charFun μ ξ‖ ^ 2 = (‖charFun ν ξ‖ ^ 2) ^ n := by
        rw [hrootξ, norm_pow]
        simp only [← pow_mul]
        congr 1
        omega
      _ ≤ (1 / 2 : ℝ) ^ n := by
        gcongr
  have hpowlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hnormsq : ‖charFun μ ξ‖ ^ 2 ≤ (0 : ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hpowlim hevent
  have hnorm : ‖charFun μ ξ‖ = 0 := by
    nlinarith [norm_nonneg (charFun μ ξ)]
  exact norm_eq_zero.mp hnorm
