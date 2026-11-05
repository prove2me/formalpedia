-- Prove2me | solution 1 for levy_foundations_arrivalSurvival
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:24.79308+00:00
-- url     : https://prove2.me/submissions/111529db-bced-482a-b7dd-6c868d9d32ce

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


lemma exp_hasDeriv (R x : ℝ) :
    HasDerivAt (fun x => Real.exp (-(R * x))) (-(R * Real.exp (-(R * x)))) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(R * x)) (-R) x := by
    have := ((hasDerivAt_id x).const_mul R).neg
    exact this.congr_deriv (by simp)
  have := h1.exp
  refine this.congr_deriv ?_
  ring

lemma survival_hasDeriv (R : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => Real.exp (-(R * x)) * ∑ k ∈ Finset.range (n + 1), (R * x) ^ k / k.factorial)
      (-(R ^ (n + 1) * x ^ n * Real.exp (-(R * x)) / n.factorial)) x := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, mul_one, pow_one]
    exact (exp_hasDeriv R x)
  | succ n ih =>
    have hp : HasDerivAt (fun x => (R * x) ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * (R * x) ^ n * R) x := by
      have := ((hasDerivAt_id x).const_mul R).pow (n + 1)
      exact this.congr_deriv (by simp)
    have hq := (exp_hasDeriv R x).mul (hp.div_const ((n + 1).factorial : ℝ))
    have hsum := ih.add hq
    have hfun : (fun x : ℝ => Real.exp (-(R * x)) *
        ∑ k ∈ Finset.range (n + 1 + 1), (R * x) ^ k / k.factorial) =
        (fun x => Real.exp (-(R * x)) * ∑ k ∈ Finset.range (n + 1), (R * x) ^ k / k.factorial) +
        (fun x => Real.exp (-(R * x))) * (fun x => (R * x) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
      funext y
      simp only [Pi.add_apply, Pi.mul_apply]
      rw [Finset.sum_range_succ _ (n + 1)]
      ring
    rw [hfun]
    refine hsum.congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma survival_tendsto (R : ℝ) (hR : 0 < R) (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => Real.exp (-(R * x)) *
      ∑ k ∈ Finset.range (n + 1), (R * x) ^ k / k.factorial) Filter.atTop (nhds 0) := by
  have hk : ∀ k : ℕ, Filter.Tendsto (fun x : ℝ => Real.exp (-(R * x)) *
      ((R * x) ^ k / k.factorial)) Filter.atTop (nhds 0) := by
    intro k
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (Filter.tendsto_id.const_mul_atTop hR)
    have h2 := h1.div_const (k.factorial : ℝ)
    simp only [zero_div] at h2
    refine h2.congr (fun x => ?_)
    simp only [Function.comp, id]
    ring
  have := tendsto_finset_sum (Finset.range (n + 1)) (fun k _ => hk k)
  simp only [Finset.sum_const_zero] at this
  refine this.congr (fun x => ?_)
  rw [Finset.mul_sum]

lemma survival_integrable (R : ℝ) (hR : 0 < R) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => R ^ (n + 1) * x ^ n * Real.exp (-(R * x)) / n.factorial) (Set.Ioi t) := by
  have hFc : Continuous (fun x : ℝ => Real.exp (-(R * x)) *
      ∑ k ∈ Finset.range (n + 1), (R * x) ^ k / k.factorial) := by fun_prop
  have := integrableOn_Ioi_deriv_of_nonneg (g := fun x => -(Real.exp (-(R * x)) *
      ∑ k ∈ Finset.range (n + 1), (R * x) ^ k / k.factorial)) (a := t)
    (g' := fun x => R ^ (n + 1) * x ^ n * Real.exp (-(R * x)) / n.factorial) (l := 0)
    hFc.neg.continuousWithinAt
    (fun x _ => (survival_hasDeriv R n x).neg.congr_deriv (neg_neg _))
    (fun x hx => by
      have : 0 ≤ x := le_trans ht (le_of_lt hx)
      positivity)
    (by simpa using (survival_tendsto R hR n).neg)
  exact this

lemma survival_integral (R : ℝ) (hR : 0 < R) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x in Set.Ioi t, R ^ (n + 1) * x ^ n * Real.exp (-(R * x)) / n.factorial =
      Real.exp (-(R * t)) * ∑ k ∈ Finset.range (n + 1), (R * t) ^ k / k.factorial := by
  have hFc : Continuous (fun x : ℝ => Real.exp (-(R * x)) *
      ∑ k ∈ Finset.range (n + 1), (R * x) ^ k / k.factorial) := by fun_prop
  have hint := survival_integrable R hR n ht
  have := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun x : ℝ => Real.exp (-(R * x)) *
      ∑ k ∈ Finset.range (n + 1), (R * x) ^ k / k.factorial)
    (f' := fun x => -(R ^ (n + 1) * x ^ n * Real.exp (-(R * x)) / n.factorial)) (a := t) (m := 0)
    hFc.continuousWithinAt (fun x _ => survival_hasDeriv R n x) hint.neg
    (survival_tendsto R hR n)
  rw [integral_neg] at this
  linarith

end Lv2Aux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (μ {ω | t < LevyFoundations.arrival τ n ω}).toReal =
      Real.exp (-(r * t)) *
        ∑ k ∈ Finset.range (n + 1), (r * t) ^ k / k.factorial := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hmeas := hd.measurable_interarrival
  have hA := Lv2Aux.arrival_meas hmeas n
  have hset : {ω | t < LevyFoundations.arrival τ n ω} = LevyFoundations.arrival τ n ⁻¹' Set.Ioi t := rfl
  rw [hset, ← Measure.map_apply hA measurableSet_Ioi, Lv2Aux.arrival_law hd hr n,
    withDensity_apply _ measurableSet_Ioi]
  have h1 : ∫⁻ x in Set.Ioi t, LevyFoundations.arrivalGammaDensity (r : ℝ) n x =
      ∫⁻ x in Set.Ioi t, ENNReal.ofReal ((r : ℝ) ^ (n + 1) * x ^ n * Real.exp (-((r : ℝ) * x)) /
        n.factorial) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact Lv2Aux.gammaDens_nonneg _ n (le_trans ht (le_of_lt hx))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi t)] (fun x : ℝ => (r : ℝ) ^ (n + 1) * x ^ n *
      Real.exp (-((r : ℝ) * x)) / n.factorial) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : 0 ≤ x := le_trans ht (le_of_lt hx)
    positivity
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal (Lv2Aux.survival_integrable _ hr' n ht) hnn,
    Lv2Aux.survival_integral _ hr' n ht, ENNReal.toReal_ofReal (by positivity)]
