-- Prove2me | solution 1 for levy_foundations_compoundPoissonMarginalInfinitelyDivisible
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:30.141333+00:00
-- url     : https://prove2.me/submissions/262beed5-b89d-472e-a4eb-842e2650f2b2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal


namespace Lv2Aux

noncomputable def arrivalGammaDensityReal (R : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  R ^ (n + 1) * s ^ n * Real.exp (-(R * s)) / n.factorial

noncomputable def arrivalGammaDensity (R : ℝ) (n : ℕ) (s : ℝ) : ENNReal :=
  (Set.Ici 0).indicator
    (fun y => ENNReal.ofReal (arrivalGammaDensityReal R n y)) s

end Lv2Aux

namespace Lv2Aux
open Filter

lemma gammaDens_neg (R : ℝ) (n : ℕ) {s : ℝ} (hs : s < 0) :
    Lv2Aux.arrivalGammaDensity R n s = 0 := by
  unfold Lv2Aux.arrivalGammaDensity
  rw [Set.indicator_of_notMem]
  simpa using hs

lemma gammaDens_nonneg (R : ℝ) (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Lv2Aux.arrivalGammaDensity R n s =
      ENNReal.ofReal (Lv2Aux.arrivalGammaDensityReal R n s) := by
  unfold Lv2Aux.arrivalGammaDensity
  rw [Set.indicator_of_mem]
  simpa using hs

lemma expMeasure_eq (R : ℝ) :
    expMeasure R = volume.withDensity (Lv2Aux.arrivalGammaDensity R 0) := by
  unfold expMeasure gammaMeasure
  congr 1
  funext x
  by_cases hx : 0 ≤ x
  · rw [gammaDens_nonneg R 0 hx, gammaPDF_of_nonneg hx]
    simp [Lv2Aux.arrivalGammaDensityReal]
  · push_neg at hx
    rw [gammaDens_neg R 0 hx, gammaPDF_of_neg hx]

lemma lconv_gamma (R : ℝ) (hR : 0 < R) (n : ℕ) (s : ℝ) :
    (Lv2Aux.arrivalGammaDensity R n ⋆ₗ Lv2Aux.arrivalGammaDensity R 0) s =
      Lv2Aux.arrivalGammaDensity R (n + 1) s := by
  unfold lconvolution
  by_cases hs : 0 ≤ s
  · set H : ℝ → ℝ := fun y => R ^ (n + 2) * Real.exp (-(R * s)) * y ^ n / n.factorial with hH
    have hint : ∀ y : ℝ, Lv2Aux.arrivalGammaDensity R n y *
        Lv2Aux.arrivalGammaDensity R 0 (-y + s) =
        (Set.Icc 0 s).indicator (fun y => ENNReal.ofReal (H y)) y := by
      intro y
      by_cases hy : 0 ≤ y
      · by_cases hys : y ≤ s
        · rw [Set.indicator_of_mem (show y ∈ Set.Icc 0 s from ⟨hy, hys⟩),
            gammaDens_nonneg R n hy, gammaDens_nonneg R 0 (by linarith)]
          rw [← ENNReal.ofReal_mul (by
            unfold Lv2Aux.arrivalGammaDensityReal; positivity)]
          congr 1
          simp only [hH, Lv2Aux.arrivalGammaDensityReal]
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
    simp only [Lv2Aux.arrivalGammaDensityReal, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · push_neg at hs
    have hz : ∀ y : ℝ, Lv2Aux.arrivalGammaDensity R n y *
        Lv2Aux.arrivalGammaDensity R 0 (-y + s) = 0 := by
      intro y
      by_cases hy : y < 0
      · rw [gammaDens_neg R n hy, zero_mul]
      · rw [gammaDens_neg R 0 (by linarith), mul_zero]
    simp [hz, gammaDens_neg R (n + 1) hs]

lemma gammaDens_meas (R : ℝ) (n : ℕ) :
    Measurable (Lv2Aux.arrivalGammaDensity R n) := by
  unfold Lv2Aux.arrivalGammaDensity
  refine Measurable.indicator ?_ measurableSet_Ici
  refine ENNReal.measurable_ofReal.comp ?_
  unfold Lv2Aux.arrivalGammaDensityReal
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
      volume.withDensity (Lv2Aux.arrivalGammaDensity (r : ℝ) n) := by
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
  have h1 : ∫⁻ x in Set.Ioi t, Lv2Aux.arrivalGammaDensity (r : ℝ) n x =
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


lemma jump_prob {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (t : ℝ≥0) (k : ℕ) :
    μ ((fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) ⁻¹' {k}) =
      ENNReal.ofReal (Real.exp (-((r : ℝ) * (t : ℝ))) * ((r : ℝ) * (t : ℝ)) ^ k /
        k.factorial) := by
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
  rw [show (fun ω => LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) = _ from rfl]
  cases k with
  | zero =>
    have : (fun ω => LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) ⁻¹' {0} =
        {ω | LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) ≤ 0} := by
      ext ω; simp
    rw [this, hle 0, survival_meas hd hr 0 ht']
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
    rw [this, measure_diff hsub hms.nullMeasurableSet, hle, hle, survival_meas hd hr _ ht',
      survival_meas hd hr _ ht', ← ENNReal.ofReal_sub _ (by positivity)]
    · congr 1
      rw [Finset.sum_range_succ _ (j + 1)]
      push_cast
      ring
    · exact measure_ne_top _ _


def blk (c : Bool) : Set (ℕ ⊕ ℕ) := cond c (Set.range Sum.inl) (Set.range Sum.inr)

end Lv2Aux

namespace Lv2Grp
open Set MeasurableSpace

lemma iIndepSets_piiUnionInter_pairwiseDisjoint
    {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {π : κ → Set (Set Ω)} {S : ι → Set κ}
    (h_indep : iIndepSets π μ)
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepSets (fun i => piiUnionInter π (S i)) μ := by
  classical
  rw [iIndepSets_iff]
  intro s A hA
  have hex : ∀ i, ∃ (t : Finset κ) (g : κ → Set Ω), i ∈ s →
      (↑t ⊆ S i ∧ (∀ k ∈ t, g k ∈ π k) ∧ A i = ⋂ k ∈ t, g k) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨t, ht, g, hg, he⟩ := hA i hi
      exact ⟨t, g, fun _ => ⟨ht, hg, he⟩⟩
    · exact ⟨∅, fun _ => ∅, fun h => absurd h hi⟩
  choose t g hg using hex
  have hdisj : Set.PairwiseDisjoint (↑s) t := by
    intro i hi j hj hij
    rw [Function.onFun, Finset.disjoint_left]
    intro k hki hkj
    exact (Set.disjoint_left.1 (hS hij) ((hg i hi).1 hki)) ((hg j hj).1 hkj)
  let G : κ → Set Ω := fun k => ⋂ i ∈ s.filter (fun i => k ∈ t i), g i k
  have hGeq : ∀ i ∈ s, ∀ k ∈ t i, G k = g i k := by
    intro i hi k hk
    have : s.filter (fun j => k ∈ t j) = {i} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hj, hkj⟩
        by_contra hne
        exact Set.disjoint_left.1 (hS hne) ((hg j hj).1 hkj) ((hg i hi).1 hk)
      · rintro rfl
        exact ⟨hi, hk⟩
    show (⋂ j ∈ s.filter (fun j => k ∈ t j), g j k) = g i k
    rw [this]
    simp
  have h1 : (⋂ i ∈ s, A i) = ⋂ k ∈ s.biUnion t, G k := by
    rw [Finset.set_biInter_biUnion]
    apply Set.iInter₂_congr
    intro i hi
    rw [(hg i hi).2.2]
    apply Set.iInter₂_congr
    intro k hk
    exact (hGeq i hi k hk).symm
  have h2 : ∀ k ∈ s.biUnion t, G k ∈ π k := by
    intro k hk
    obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.1 hk
    rw [hGeq i hi k hki]
    exact (hg i hi).2.1 k hki
  rw [h1, h_indep.meas_biInter _ h2, Finset.prod_biUnion hdisj]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(hg i hi).2.2, h_indep.meas_biInter (t i) (fun k hk => (hg i hi).2.1 k hk)]
  apply Finset.prod_congr rfl
  intro k hk
  rw [hGeq i hi k hk]


lemma iIndepFun_setRestrict_pairwiseDisjoint
    {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {β : κ → Type*} {mβ : ∀ k, MeasurableSpace (β k)}
    {f : ∀ k, Ω → β k} (hf : ∀ k, Measurable (f k))
    (h_indep : iIndepFun f μ) {S : ι → Set κ}
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepFun (fun i ω => (S i).restrict fun k => f k ω) μ := by
  have h0 := iIndepSets_piiUnionInter_pairwiseDisjoint
    (π := fun k => {s | MeasurableSet[(mβ k).comap (f k)] s}) (S := S)
    (h_indep.iIndep.iIndepSets') hS
  rw [iIndepFun_iff_iIndep (fun i => MeasurableSpace.pi) _ μ]
  have hcomap : ∀ i, MeasurableSpace.comap (fun ω => (S i).restrict fun k => f k ω)
      MeasurableSpace.pi = ⨆ k ∈ S i, (mβ k).comap (f k) := by
    intro i
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, iSup_subtype']
    apply iSup_congr
    intro k
    rw [MeasurableSpace.comap_comp]
    rfl
  refine iIndepSets.iIndep (h_le := ?_) (π := _) (h_pi := ?_) (h_generate := ?_) (h_ind := h0)
  · intro i
    have : Measurable (fun ω => (S i).restrict fun k => f k ω) :=
      measurable_pi_iff.2 fun k => hf k
    exact this.comap_le
  · intro i
    exact isPiSystem_piiUnionInter _ (fun k => @MeasurableSpace.isPiSystem_measurableSet Ω ((mβ k).comap (f k))) _
  · intro i
    rw [hcomap i]
    exact (generateFrom_piiUnionInter_measurableSet (fun k => (mβ k).comap (f k)) (S i)).symm


end Lv2Grp


lemma Lv2Aux.cp_meas
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (b : ℝ) (t : ℝ≥0) :
    Measurable (LevyFoundations.compoundPoisson b τ Y (t : ℝ)) := by
  have hmeasτ := hd.measurable_interarrival
  have hmeasY := hd.measurable_mark
  have hA := Lv2Aux.arrival_meas hmeasτ
  -- the jump counting variable
  set N : Ω → ℕ := fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) with hN
  have hNm : Measurable N := Lv2Aux.jc_meas (fun n => LevyFoundations.arrival τ n) hA (t : ℝ)
  have hZ : ∀ ω, LevyFoundations.compoundPoisson b τ Y (t : ℝ) ω =
      b * t + ∑ i ∈ Finset.range (N ω), Y i ω := by
    intro ω
    simp [LevyFoundations.compoundPoisson, LevyFoundations.piecewisePath, hN]
  have hZm : Measurable (LevyFoundations.compoundPoisson b τ Y (t : ℝ)) := by
    have h1 : Measurable (fun p : ℕ × Ω => ∑ i ∈ Finset.range p.1, Y i p.2) :=
      measurable_from_prod_countable_right fun n =>
        (Finset.measurable_sum (Finset.range n) fun i _ => hmeasY i :
          Measurable fun y => ∑ i ∈ Finset.range n, Y i y)
    have h2 := h1.comp (hNm.prodMk measurable_id)
    have h3 : LevyFoundations.compoundPoisson b τ Y (t : ℝ) =
        fun ω => b * t + (fun p : ℕ × Ω => ∑ i ∈ Finset.range p.1, Y i p.2) (N ω, ω) := by
      funext ω; exact hZ ω
    rw [h3]
    exact measurable_const.add h2
  exact hZm

lemma Lv2Aux.compound_charFun
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ))) ξ =
      Complex.exp ((t : ℝ) * (Complex.I * b * ξ +
        r * (charFun ν' ξ - 1))) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hmeasτ := hd.measurable_interarrival
  have hmeasY := hd.measurable_mark
  have hA := Lv2Aux.arrival_meas hmeasτ
  -- the jump counting variable
  set N : Ω → ℕ := fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ) with hN
  have hNm : Measurable N := Lv2Aux.jc_meas (fun n => LevyFoundations.arrival τ n) hA (t : ℝ)
  have hZ : ∀ ω, LevyFoundations.compoundPoisson b τ Y (t : ℝ) ω =
      b * t + ∑ i ∈ Finset.range (N ω), Y i ω := by
    intro ω
    simp [LevyFoundations.compoundPoisson, LevyFoundations.piecewisePath, hN]
  have hZm : Measurable (LevyFoundations.compoundPoisson b τ Y (t : ℝ)) := by
    have h1 : Measurable (fun p : ℕ × Ω => ∑ i ∈ Finset.range p.1, Y i p.2) :=
      measurable_from_prod_countable_right fun n =>
        (Finset.measurable_sum (Finset.range n) fun i _ => hmeasY i :
          Measurable fun y => ∑ i ∈ Finset.range n, Y i y)
    have h2 := h1.comp (hNm.prodMk measurable_id)
    have h3 : LevyFoundations.compoundPoisson b τ Y (t : ℝ) =
        fun ω => b * t + (fun p : ℕ × Ω => ∑ i ∈ Finset.range p.1, Y i p.2) (N ω, ω) := by
      funext ω; exact hZ ω
    rw [h3]
    exact measurable_const.add h2
  -- independence of the sequences
  have hall : ∀ k : ℕ ⊕ ℕ, Measurable (Sum.elim τ Y k) := by
    intro k; cases k with
    | inl n => exact hmeasτ n
    | inr n => exact hmeasY n
  have hS : Pairwise (Function.onFun Disjoint Lv2Aux.blk) := by
    intro i j hij
    cases i <;> cases j
    · exact absurd rfl hij
    · refine Set.disjoint_left.2 ?_
      rintro x ⟨a, rfl⟩ ⟨c, hc⟩
      cases hc
    · refine Set.disjoint_left.2 ?_
      rintro x ⟨a, rfl⟩ ⟨c, hc⟩
      cases hc
    · exact absurd rfl hij
  have hgroup := Lv2Grp.iIndepFun_setRestrict_pairwiseDisjoint hall hd.indep hS
  have hTT := hgroup.indepFun (by decide : true ≠ false)
  have hGτm : Measurable (fun (x : ↥(Lv2Aux.blk true) → ℝ) (i : ℕ) =>
      x ⟨Sum.inl i, (show Sum.inl i ∈ Set.range (Sum.inl : ℕ → ℕ ⊕ ℕ) from ⟨i, rfl⟩)⟩) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hGYm : Measurable (fun (x : ↥(Lv2Aux.blk false) → ℝ) (i : ℕ) =>
      x ⟨Sum.inr i, (show Sum.inr i ∈ Set.range (Sum.inr : ℕ → ℕ ⊕ ℕ) from ⟨i, rfl⟩)⟩) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hindTY : IndepFun (fun ω (i : ℕ) => τ i ω) (fun ω (i : ℕ) => Y i ω) μ :=
    hTT.comp hGτm hGYm
  have hindY : iIndepFun Y μ := hd.indep.precomp (g := Sum.inr) Sum.inr_injective
  set φ : ℂ := charFun ν' ξ with hφ
  set c : ℂ := Complex.exp (↑ξ * ↑(b * (t : ℝ)) * Complex.I) with hc
  set p : ℕ → ℝ := fun k => Real.exp (-((r : ℝ) * t)) * (((r : ℝ) * t) ^ k / k.factorial) with hp
  have hp_nonneg : ∀ k, 0 ≤ p k := by intro k; simp only [hp]; positivity
  have hpreal : ∀ k, μ.real (N ⁻¹' {k}) = p k := by
    intro k
    have h1 : μ (N ⁻¹' {k}) = ENNReal.ofReal (p k) := by
      have := Lv2Aux.jump_prob hd hr t k
      rw [show N ⁻¹' {k} = (fun ω => LevyFoundations.jumpCount
        (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) ⁻¹' {k} from rfl, this]
      congr 1
      simp only [hp]
      ring
    rw [measureReal_def, h1, ENNReal.toReal_ofReal (hp_nonneg k)]
  let U : ℕ → Ω → ℂ := fun k ω => if N ω = k then c else 0
  let V : ℕ → Ω → ℂ := fun k ω =>
    Complex.exp (↑ξ * ↑(∑ i ∈ Finset.range k, Y i ω) * Complex.I)
  let f : Ω → ℂ := fun ω =>
    Complex.exp (↑ξ * ↑(LevyFoundations.compoundPoisson b τ Y (t : ℝ) ω) * Complex.I)
  have hF : ∀ k ω, (if N ω = k then f ω else 0) = U k ω * V k ω := by
    intro k ω
    by_cases hk : N ω = k
    · simp only [U, V, f, hk, if_true]
      rw [hZ ω, hk, hc, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [U, hk]
  have hUm : ∀ k, Measurable (U k) := fun k =>
    Measurable.ite (hNm (measurableSet_singleton k)) measurable_const measurable_const
  have hVm : ∀ k, Measurable (V k) := by
    intro k
    have := Finset.measurable_sum (Finset.range k) (fun i _ => hmeasY i)
    simp only [V]
    fun_prop
  have hUV : ∀ k, IndepFun (U k) (V k) μ := by
    intro k
    have hj := Lv2Aux.jc_meas (Ω := ℕ → ℝ) (fun n x => ∑ i ∈ Finset.range (n + 1), x i)
      (fun n => Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) (t : ℝ)
    have hgm : Measurable (fun x : ℕ → ℝ => if LevyFoundations.jumpCount
        (fun n => ∑ i ∈ Finset.range (n + 1), x i) (t : ℝ) = k then c else 0) :=
      Measurable.ite (hj (measurableSet_singleton k)) measurable_const measurable_const
    have hhm : Measurable (fun y : ℕ → ℝ =>
        Complex.exp (↑ξ * ↑(∑ i ∈ Finset.range k, y i) * Complex.I)) := by
      have := Finset.measurable_sum (Finset.range k) (fun i _ => measurable_pi_apply (X := fun _ : ℕ => ℝ) i)
      fun_prop
    exact hindTY.comp hgm hhm
  have hIU : ∀ k, ∫ ω, U k ω ∂μ = (p k : ℂ) * c := by
    intro k
    have : U k = (N ⁻¹' {k}).indicator (fun _ => c) := by
      funext ω
      by_cases hk : N ω = k
      · rw [Set.indicator_of_mem (show ω ∈ N ⁻¹' {k} from hk)]; simp [U, hk]
      · rw [Set.indicator_of_notMem (show ω ∉ N ⁻¹' {k} from hk)]; simp [U, hk]
    rw [this, integral_indicator_const c (hNm (measurableSet_singleton k)), hpreal,
      Complex.real_smul]
  have hIV : ∀ k, ∫ ω, V k ω ∂μ = φ ^ k := by
    intro k
    have hsm := Finset.measurable_sum (Finset.range k) (fun i _ => hmeasY i)
    have h1 : ∫ ω, V k ω ∂μ = charFun (μ.map (fun ω => ∑ i ∈ Finset.range k, Y i ω)) ξ := by
      rw [charFun_apply_real, integral_map hsm.aemeasurable (by fun_prop)]
    rw [h1, iIndepFun.charFun_map_fun_finsetSum_eq_prod (fun i _ => (hmeasY i).aemeasurable)
      (iIndepFun_iff_finset.1 hindY _)]
    rw [Finset.prod_congr rfl (fun i _ => by rw [(hd.law_mark i).map_eq]), Finset.prod_const,
      Finset.card_range, Pi.pow_apply]
  have hIF : ∀ k, ∫ ω, (if N ω = k then f ω else 0) ∂μ = (p k : ℂ) * c * φ ^ k := by
    intro k
    simp_rw [hF]
    have := (hUV k).integral_mul_eq_mul_integral (hUm k).aestronglyMeasurable
      (hVm k).aestronglyMeasurable
    rw [show (fun ω => U k ω * V k ω) = U k * V k from rfl, this, hIU, hIV]
  have hfnorm : ∀ ω, ‖f ω‖ = 1 := by
    intro ω
    have := Complex.norm_exp_ofReal_mul_I (ξ * LevyFoundations.compoundPoisson b τ Y (t : ℝ) ω)
    push_cast at this
    exact this
  have hFm : ∀ k, Measurable (fun ω => if N ω = k then f ω else 0) := by
    intro k
    have : (fun ω => if N ω = k then f ω else 0) = fun ω => U k ω * V k ω := funext (hF k)
    rw [this]
    exact (hUm k).mul (hVm k)
  have hFint : ∀ k, Integrable (fun ω => if N ω = k then f ω else 0) μ := by
    intro k
    refine Integrable.of_bound (hFm k).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hk : N ω = k
    · simp [hk, hfnorm]
    · simp [hk]
  have hnormeq : ∀ k, ∫ ω, ‖(if N ω = k then f ω else 0)‖ ∂μ = p k := by
    intro k
    have : (fun ω => ‖(if N ω = k then f ω else 0)‖) =
        (N ⁻¹' {k}).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hk : N ω = k
      · rw [Set.indicator_of_mem (show ω ∈ N ⁻¹' {k} from hk)]; simp [hk, hfnorm]
      · rw [Set.indicator_of_notMem (show ω ∉ N ⁻¹' {k} from hk)]; simp [hk]
    rw [this, integral_indicator_const _ (hNm (measurableSet_singleton k)), hpreal]
    simp
  have hpsum : Summable p := by
    have := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * t)).summable.mul_left
      (Real.exp (-((r : ℝ) * t)))
    exact this
  have hHS := hasSum_integral_of_summable_integral_norm hFint
    (by simpa only [hnormeq] using hpsum)
  have hsumeq : ∀ ω, ∑' k, (if N ω = k then f ω else 0) = f ω := by
    intro ω
    rw [tsum_eq_single (N ω) (fun k hk => by simp [Ne.symm hk])]
    simp
  simp_rw [hsumeq] at hHS
  have hexp := (NormedSpace.expSeries_div_hasSum_exp (((r : ℝ) * t : ℝ) * φ : ℂ)).mul_left
    (c * Complex.exp (-(((r : ℝ) * t : ℝ) : ℂ)))
  have hHS2 : HasSum (fun k => ∫ ω, (if N ω = k then f ω else 0) ∂μ)
      (c * Complex.exp (-(((r : ℝ) * t : ℝ) : ℂ)) *
        NormedSpace.exp ((((r : ℝ) * t : ℝ) : ℂ) * φ)) := by
    have hfun : (fun k => ∫ ω, (if N ω = k then f ω else 0) ∂μ) =
        fun n : ℕ => c * Complex.exp (-(((r : ℝ) * t : ℝ) : ℂ)) *
          (((((r : ℝ) * t : ℝ) : ℂ) * φ) ^ n / (n.factorial : ℂ)) := by
      funext k
      rw [hIF k]
      simp only [hp]
      push_cast
      rw [mul_pow]
      ring
    rw [hfun]
    exact hexp
  have hint := hHS.unique hHS2
  have hcf : charFun (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ))) ξ = ∫ ω, f ω ∂μ := by
    rw [charFun_apply_real, integral_map hZm.aemeasurable (by fun_prop)]
  rw [hcf, hint, ← Complex.exp_eq_exp_ℂ, hc, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring


theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν']
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0) (b : ℝ) (t : ℝ≥0) :
    LevyFoundations.isInfinitelyDivisible
      (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ))) := by
  intro n hn
  have hn' : (0:ℝ) < n := Nat.cast_pos.2 hn
  set s : ℝ≥0 := t / n with hs
  have hns : (n : ℝ) * (s : ℝ) = (t : ℝ) := by
    rw [hs]; push_cast; field_simp
  have hcm := Lv2Aux.cp_meas hd b s
  have hprob : IsProbabilityMeasure (μ.map (LevyFoundations.compoundPoisson b τ Y (s : ℝ))) :=
    Measure.isProbabilityMeasure_map hcm.aemeasurable
  have hpow : ∀ k : ℕ, IsProbabilityMeasure
      (LevyFoundations.iteratedConv (μ.map (LevyFoundations.compoundPoisson b τ Y (s : ℝ))) k) ∧
      charFun (LevyFoundations.iteratedConv
        (μ.map (LevyFoundations.compoundPoisson b τ Y (s : ℝ))) k) =
      charFun (μ.map (LevyFoundations.compoundPoisson b τ Y (s : ℝ))) ^ k := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [LevyFoundations.iteratedConv]; infer_instance
      · funext ξ
        simp [LevyFoundations.iteratedConv, charFun_dirac]
    | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · simp only [LevyFoundations.iteratedConv]; infer_instance
      · funext ξ
        simp only [LevyFoundations.iteratedConv]
        rw [charFun_conv, ih2, pow_succ']
        rfl
  refine ⟨μ.map (LevyFoundations.compoundPoisson b τ Y (s : ℝ)), hprob, ?_⟩
  haveI := (hpow n).1
  apply Measure.ext_of_charFun
  funext ξ
  rw [(hpow n).2, Pi.pow_apply, Lv2Aux.compound_charFun hd hr b s ξ,
    Lv2Aux.compound_charFun hd hr b t ξ, ← Complex.exp_nat_mul]
  congr 1
  rw [← hns]
  push_cast
  ring
