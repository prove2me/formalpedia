-- Prove2me | solution 1 for levy_foundations_arrivalGammaLaw
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:23.976499+00:00
-- url     : https://prove2.me/submissions/ab193643-930c-477d-89b7-acffc41b7fdf

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrivalGammaDensityReal
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Definitions.Def_levy_foundations_arrivalSurvivalPolynomial
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal

namespace Lv2Aux

lemma gammaDens_neg (R : ℝ) (n : ℕ) {s : ℝ} (hs : s < 0) :
    LevyFoundations.arrivalGammaDensity R n s = 0 := by
  unfold LevyFoundations.arrivalGammaDensity
  rw [Set.indicator_of_notMem]
  simpa using hs

lemma gammaDens_nonneg (R : ℝ) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    LevyFoundations.arrivalGammaDensity R n s =
      ENNReal.ofReal (LevyFoundations.arrivalGammaDensityReal R n s) := by
  unfold LevyFoundations.arrivalGammaDensity
  rw [Set.indicator_of_mem]
  simpa using hs

lemma expMeasure_eq (R : ℝ) :
    expMeasure R = volume.withDensity (LevyFoundations.arrivalGammaDensity R 0) := by
  unfold expMeasure gammaMeasure
  congr 1
  funext x
  by_cases hx : 0 ≤ x
  · rw [gammaDens_nonneg R 0 hx, gammaPDF_of_nonneg hx]
    simp [LevyFoundations.arrivalGammaDensityReal]
  · push_neg at hx
    rw [gammaDens_neg R 0 hx, gammaPDF_of_neg hx]

lemma lconv_gamma (R : ℝ) (hR : 0 < R) (n : ℕ) (s : ℝ) :
    (LevyFoundations.arrivalGammaDensity R n ⋆ₗ LevyFoundations.arrivalGammaDensity R 0) s =
      LevyFoundations.arrivalGammaDensity R (n + 1) s := by
  unfold lconvolution
  by_cases hs : 0 ≤ s
  · set H : ℝ → ℝ := fun y => R ^ (n + 2) * Real.exp (-(R * s)) * y ^ n / n.factorial with hH
    have hint : ∀ y : ℝ, LevyFoundations.arrivalGammaDensity R n y *
        LevyFoundations.arrivalGammaDensity R 0 (-y + s) =
        (Set.Icc 0 s).indicator (fun y => ENNReal.ofReal (H y)) y := by
      intro y
      by_cases hy : 0 ≤ y
      · by_cases hys : y ≤ s
        · rw [Set.indicator_of_mem (show y ∈ Set.Icc 0 s from ⟨hy, hys⟩),
            gammaDens_nonneg R n hy, gammaDens_nonneg R 0 (by linarith)]
          rw [← ENNReal.ofReal_mul (by
            unfold LevyFoundations.arrivalGammaDensityReal; positivity)]
          congr 1
          simp only [hH, LevyFoundations.arrivalGammaDensityReal]
          have : Real.exp (-(R * (-y + s))) * Real.exp (-(R * y)) = Real.exp (-(R * s)) := by
            rw [← Real.exp_add]; congr 1; ring
          simp only [zero_add, pow_one, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
            div_one, pow_succ]
          rw [← this]
          ring
        · push_neg at hys
          rw [Set.indicator_of_notMem (by simp [hys.not_ge]), gammaDens_neg R 0 (by linarith)]
          simp
      · push_neg at hy
        rw [Set.indicator_of_notMem (by simp [hy.not_ge]), gammaDens_neg R n hy]
        simp
    simp_rw [hint]
    rw [lintegral_indicator measurableSet_Icc, gammaDens_nonneg R (n + 1) hs]
    have hcont : Continuous H := by
      simp only [hH]; fun_prop
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 s)] H := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      have := hy.1
      simp only [hH]
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc) hnn]
    congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    simp only [hH]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    simp only [LevyFoundations.arrivalGammaDensityReal, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · push_neg at hs
    have hz : ∀ y : ℝ, LevyFoundations.arrivalGammaDensity R n y *
        LevyFoundations.arrivalGammaDensity R 0 (-y + s) = 0 := by
      intro y
      by_cases hy : y < 0
      · rw [gammaDens_neg R n hy, zero_mul]
      · rw [gammaDens_neg R 0 (by linarith), mul_zero]
    simp [hz, gammaDens_neg R (n + 1) hs]

lemma gammaDens_meas (R : ℝ) (n : ℕ) :
    Measurable (LevyFoundations.arrivalGammaDensity R n) := by
  unfold LevyFoundations.arrivalGammaDensity
  refine Measurable.indicator ?_ measurableSet_Ici
  refine ENNReal.measurable_ofReal.comp ?_
  unfold LevyFoundations.arrivalGammaDensityReal
  fun_prop

lemma driver_indep_tau {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) : iIndepFun τ μ :=
  h.indep.precomp (g := Sum.inl) Sum.inl_injective

lemma arrival_meas {Ω : Type*} [MeasurableSpace Ω] {τ : ℕ → Ω → ℝ}
    (hmeas : ∀ n, Measurable (τ n)) (n : ℕ) : Measurable (LevyFoundations.arrival τ n) := by
  unfold LevyFoundations.arrival
  exact Finset.measurable_sum _ fun i _ => hmeas i

lemma arrival_law {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) :
    μ.map (LevyFoundations.arrival τ n) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity (r : ℝ) n) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hmeas := hd.measurable_interarrival
  have hind : iIndepFun τ μ := driver_indep_tau hd
  induction n with
  | zero =>
    have : LevyFoundations.arrival τ 0 = τ 0 := by funext ω; simp [LevyFoundations.arrival]
    rw [this, (hd.law_interarrival 0).map_eq, expMeasure_eq]
  | succ n ih =>
    have e : LevyFoundations.arrival τ (n + 1) =
        LevyFoundations.arrival τ n + τ (n + 1) := by
      funext ω; simp [LevyFoundations.arrival, Finset.sum_range_succ]
    have hI : IndepFun (LevyFoundations.arrival τ n) (τ (n + 1)) μ := by
      have := hind.indepFun_finsetSum_of_notMem hmeas (s := Finset.range (n + 1)) (i := n + 1)
        (by simp)
      convert this using 1
      funext ω
      simp [LevyFoundations.arrival, Finset.sum_apply]
    rw [e, hI.map_add_eq_map_conv_map₀ (arrival_meas hmeas n).aemeasurable (hmeas _).aemeasurable,
      ih, (hd.law_interarrival (n + 1)).map_eq, expMeasure_eq,
      conv_withDensity_eq_lconvolution (gammaDens_meas _ _) (gammaDens_meas _ _)]
    congr 1
    funext s
    exact lconv_gamma _ hr' n s

end Lv2Aux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) :
    μ.map (LevyFoundations.arrival τ n) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity (r : ℝ) n) := by
  exact Lv2Aux.arrival_law hd hr n
