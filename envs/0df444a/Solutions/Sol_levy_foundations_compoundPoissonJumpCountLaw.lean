-- Prove2me | solution 1 for levy_foundations_compoundPoissonJumpCountLaw
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:25.923807+00:00
-- url     : https://prove2.me/submissions/4b2aa2c4-e0eb-44e5-83b4-498f1ec2d038

import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Poisson.Basic
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


lemma expMeasure_Iio_zero (r : ℝ) : expMeasure r (Set.Iio (0:ℝ)) = 0 := by
  unfold expMeasure gammaMeasure
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos le_rfl

lemma expMeasure_Iic_lt {r : ℝ} (hr : 0 < r) (M : ℝ) (hM : 0 ≤ M) :
    expMeasure r (Set.Iic M) < 1 := by
  have := isProbabilityMeasure_expMeasure hr
  have h1 := cdf_expMeasure_eq hr M
  rw [ProbabilityTheory.cdf_eq_real] at h1
  have h3 : (expMeasure r).real (Set.Iic M) < 1 := by
    rw [h1, if_pos hM]; simp; positivity
  rw [measureReal_def] at h3
  have := (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one)).2 h3
  rwa [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_one] at this


lemma arrival_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => LevyFoundations.arrival τ n ω) atTop atTop := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have : IsProbabilityMeasure μ :=
    (h.law_interarrival 0).isProbabilityMeasure_iff.2 (isProbabilityMeasure_expMeasure hr')
  have hmeasτ := h.measurable_interarrival
  have hind := driver_indep_tau h
  have hnn : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ τ i ω := by
    rw [ae_all_iff]
    intro i
    have h0 : μ {a | τ i a < 0} = 0 := by
      have : {a | τ i a < 0} = τ i ⁻¹' Set.Iio 0 := rfl
      rw [this, ← Measure.map_apply (hmeasτ i) measurableSet_Iio, (h.law_interarrival i).map_eq]
      exact expMeasure_Iio_zero _
    rw [ae_iff]
    simpa [not_le] using h0
  -- for each M, P(∀ i, τ i ≤ M) = 0
  have hM : ∀ M : ℕ, μ (⋂ i, τ i ⁻¹' Set.Iic (M : ℝ)) = 0 := by
    intro M
    set c := expMeasure (r : ℝ) (Set.Iic (M : ℝ)) with hc
    have hc1 : c < 1 := expMeasure_Iic_lt hr' M (by positivity)
    have hτ : ∀ i, μ (τ i ⁻¹' Set.Iic (M : ℝ)) = c := by
      intro i
      rw [← Measure.map_apply (hmeasτ i) measurableSet_Iic, (h.law_interarrival i).map_eq]
    have hpow : ∀ n : ℕ, μ (⋂ i, τ i ⁻¹' Set.Iic (M : ℝ)) ≤ c ^ (n + 1) := by
      intro n
      calc μ (⋂ i, τ i ⁻¹' Set.Iic (M : ℝ))
          ≤ μ (⋂ i ∈ Finset.range (n + 1), τ i ⁻¹' Set.Iic (M : ℝ)) := by
            apply measure_mono
            intro x hx
            simp only [Set.mem_iInter] at hx ⊢
            exact fun i _ => hx i
        _ = ∏ i ∈ Finset.range (n + 1), μ (τ i ⁻¹' Set.Iic (M : ℝ)) := by
            apply hind.meas_biInter
            intro i _
            exact ⟨Set.Iic (M : ℝ), measurableSet_Iic, rfl⟩
        _ = c ^ (n + 1) := by
            rw [Finset.prod_congr rfl (fun i _ => hτ i), Finset.prod_const, Finset.card_range]
    have hlim : Tendsto (fun n : ℕ => c ^ (n + 1)) atTop (nhds 0) :=
      (tendsto_add_atTop_iff_nat 1).2 (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc1)
    exact le_antisymm (ge_of_tendsto' hlim hpow) bot_le
  have hae : ∀ᵐ ω ∂μ, ∀ M : ℕ, ω ∉ ⋂ i, τ i ⁻¹' Set.Iic (M : ℝ) := by
    rw [ae_all_iff]
    intro M
    exact (measure_eq_zero_iff_ae_notMem).1 (hM M)
  filter_upwards [hnn, hae] with ω h1 h2
  have hmono : Monotone (fun n => LevyFoundations.arrival τ n ω) := by
    apply monotone_nat_of_le_succ
    intro n
    unfold LevyFoundations.arrival
    rw [Finset.sum_range_succ _ (n + 1)]
    linarith [h1 (n + 1)]
  refine tendsto_atTop_atTop_of_monotone hmono fun b => ?_
  by_contra hcon
  push_neg at hcon
  apply h2 ⌈b⌉₊
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
  intro i
  have h3 : τ i ω ≤ LevyFoundations.arrival τ i ω := by
    unfold LevyFoundations.arrival
    exact Finset.single_le_sum (f := fun j => τ j ω) (fun j _ => h1 j)
      (Finset.mem_range.2 (Nat.lt_succ_self i))
  linarith [hcon i, Nat.le_ceil b]

lemma jc_le_iff (a : ℕ → ℝ) (hmono : Monotone a) (hdiv : Tendsto a atTop atTop) (t : ℝ) (k : ℕ) :
    sInf {n | t < a n} ≤ k ↔ t < a k := by
  have hne : {n | t < a n}.Nonempty := by
    obtain ⟨n, hn⟩ := (hdiv.eventually (eventually_gt_atTop t)).exists
    exact ⟨n, hn⟩
  constructor
  · intro h
    exact lt_of_lt_of_le (Nat.sInf_mem hne) (hmono h)
  · intro h
    exact Nat.sInf_le h

lemma jc_eq_iff (a : ℕ → ℝ) (t : ℝ) (k : ℕ) :
    sInf {n | t < a n} = k ↔ (t < a k ∧ ∀ j < k, ¬ t < a j) ∨ (k = 0 ∧ ∀ n, ¬ t < a n) := by
  by_cases hne : {n | t < a n}.Nonempty
  · constructor
    · intro h
      left
      have hm := Nat.sInf_mem hne
      rw [h] at hm
      refine ⟨hm, fun j hj => ?_⟩
      exact Nat.notMem_of_lt_sInf (s := {n | t < a n}) (by rw [h]; exact hj)
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · apply le_antisymm (Nat.sInf_le h1)
        by_contra hlt
        push_neg at hlt
        exact h2 _ hlt (Nat.sInf_mem hne)
      · obtain ⟨n, hn⟩ := hne
        exact absurd hn (h2 n)
  · have hemp : {n | t < a n} = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    rw [hemp, Nat.sInf_empty]
    constructor
    · intro h
      right
      exact ⟨h.symm, fun n hn => hne ⟨n, hn⟩⟩
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact absurd ⟨k, h1⟩ hne
      · exact h1.symm

lemma jc_meas {Ω : Type*} [MeasurableSpace Ω] (a : ℕ → Ω → ℝ) (ha : ∀ n, Measurable (a n)) (t : ℝ) :
    Measurable (fun ω => LevyFoundations.jumpCount (fun n => a n ω) t) := by
  apply measurable_to_countable'
  intro k
  have : (fun ω => LevyFoundations.jumpCount (fun n => a n ω) t) ⁻¹' {k} =
      {ω | (t < a k ω ∧ ∀ j < k, ¬ t < a j ω) ∨ (k = 0 ∧ ∀ n, ¬ t < a n ω)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact jc_eq_iff (fun n => a n ω) t k
  rw [this]
  have hlt : ∀ j, MeasurableSet {ω | t < a j ω} := fun j => measurableSet_lt measurable_const (ha j)
  have hA : {ω | t < a k ω ∧ ∀ j < k, ¬ t < a j ω} =
      {ω | t < a k ω} ∩ ⋂ j, ⋂ (_ : j < k), {ω | t < a j ω}ᶜ := by
    ext ω; simp
  have hB : {ω | k = 0 ∧ ∀ n, ¬ t < a n ω} = {ω | k = 0} ∩ ⋂ n, {ω | t < a n ω}ᶜ := by
    ext ω; simp
  have hU : {ω | (t < a k ω ∧ ∀ j < k, ¬ t < a j ω) ∨ (k = 0 ∧ ∀ n, ¬ t < a n ω)} =
      {ω | t < a k ω ∧ ∀ j < k, ¬ t < a j ω} ∪ {ω | k = 0 ∧ ∀ n, ¬ t < a n ω} := rfl
  rw [hU, hA, hB]
  refine MeasurableSet.union ?_ ?_
  · exact (hlt k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hlt j).compl)
  · exact (MeasurableSet.const _).inter (MeasurableSet.iInter fun j => (hlt j).compl)

lemma tau_nonneg_ae {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) :
    ∀ᵐ ω ∂μ, ∀ i, 0 ≤ τ i ω := by
  rw [ae_all_iff]
  intro i
  have h0 : μ {a | τ i a < 0} = 0 := by
    have : {a | τ i a < 0} = τ i ⁻¹' Set.Iio 0 := rfl
    rw [this, ← Measure.map_apply (hd.measurable_interarrival i) measurableSet_Iio,
      (hd.law_interarrival i).map_eq]
    exact expMeasure_Iio_zero _
  rw [ae_iff]
  simpa [not_le] using h0

lemma survival_meas {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    μ {ω | t < LevyFoundations.arrival τ n ω} =
      ENNReal.ofReal (Real.exp (-(r * t)) *
        ∑ k ∈ Finset.range (n + 1), (r * t) ^ k / k.factorial) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hmeas := hd.measurable_interarrival
  have hA := arrival_meas hmeas n
  have hset : {ω | t < LevyFoundations.arrival τ n ω} =
      LevyFoundations.arrival τ n ⁻¹' Set.Ioi t := rfl
  rw [hset, ← Measure.map_apply hA measurableSet_Ioi, arrival_law hd hr n,
    withDensity_apply _ measurableSet_Ioi]
  have h1 : ∫⁻ x in Set.Ioi t, LevyFoundations.arrivalGammaDensity (r : ℝ) n x =
      ∫⁻ x in Set.Ioi t, ENNReal.ofReal ((r : ℝ) ^ (n + 1) * x ^ n * Real.exp (-((r : ℝ) * x)) /
        n.factorial) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact gammaDens_nonneg _ n (le_trans ht (le_of_lt hx))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi t)] (fun x : ℝ => (r : ℝ) ^ (n + 1) * x ^ n *
      Real.exp (-((r : ℝ) * x)) / n.factorial) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have : 0 ≤ x := le_trans ht (le_of_lt hx)
    positivity
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal (survival_integrable _ hr' n ht) hnn,
    survival_integral _ hr' n ht]

end Lv2Aux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (t : ℝ≥0) :
    μ.map (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) =
        poissonMeasure (r * t) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hmeas := hd.measurable_interarrival
  have hA := Lv2Aux.arrival_meas hmeas
  have ht' : (0:ℝ) ≤ (t : ℝ) := t.2
  have hNm : Measurable (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) :=
    Lv2Aux.jc_meas (fun n => LevyFoundations.arrival τ n) hA (t : ℝ)
  have hnn := Lv2Aux.tau_nonneg_ae hd
  have hdiv := Lv2Aux.arrival_tendsto hd hr
  have hle : ∀ k : ℕ, μ {ω | LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) ≤ k} =
      μ {ω | (t : ℝ) < LevyFoundations.arrival τ k ω} := by
    intro k
    apply measure_congr
    filter_upwards [hnn, hdiv] with ω h1 h2
    have hmono : Monotone (fun n => LevyFoundations.arrival τ n ω) := by
      apply monotone_nat_of_le_succ
      intro n
      unfold LevyFoundations.arrival
      rw [Finset.sum_range_succ _ (n + 1)]
      linarith [h1 (n + 1)]
    exact propext (Lv2Aux.jc_le_iff _ hmono h2 (t : ℝ) k)
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.map_apply hNm (measurableSet_singleton k), poissonMeasure_singleton]
  push_cast
  cases k with
  | zero =>
    have : (fun ω => LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) ⁻¹' {0} =
        {ω | LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) ≤ 0} := by
      ext ω; simp
    rw [this, hle 0, Lv2Aux.survival_meas hd hr 0 ht']
    simp
  | succ j =>
    have hsub : {ω | LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) ≤ j}
        ⊆ {ω | LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) ≤ j + 1} :=
      fun ω hω => le_trans hω (Nat.le_succ j)
    have : (fun ω => LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) ⁻¹' {j + 1} =
        {ω | LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) ≤ j + 1} \
        {ω | LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) ≤ j} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]; omega
    have hms : MeasurableSet {ω | LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) ≤ j} :=
      hNm measurableSet_Iic
    rw [this, measure_diff hsub hms.nullMeasurableSet, hle, hle, Lv2Aux.survival_meas hd hr _ ht',
      Lv2Aux.survival_meas hd hr _ ht', ← ENNReal.ofReal_sub _ (by positivity)]
    · congr 1
      rw [Finset.sum_range_succ _ (j + 1)]
      push_cast
      ring
    · exact measure_ne_top _ _
