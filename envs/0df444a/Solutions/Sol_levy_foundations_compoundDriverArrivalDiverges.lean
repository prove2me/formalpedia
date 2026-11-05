-- Prove2me | solution 1 for levy_foundations_compoundDriverArrivalDiverges
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:26.921964+00:00
-- url     : https://prove2.me/submissions/ed9bae04-c7d2-4c24-b630-27a51e2cbd9e

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Lv2Aux

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

lemma driver_indep_tau {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) : iIndepFun τ μ :=
  h.indep.precomp (g := Sum.inl) Sum.inl_injective

end Lv2Aux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω}
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => LevyFoundations.arrival τ n ω) atTop atTop := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have : IsProbabilityMeasure μ :=
    (h.law_interarrival 0).isProbabilityMeasure_iff.2 (isProbabilityMeasure_expMeasure hr')
  have hmeasτ := h.measurable_interarrival
  have hind := Lv2Aux.driver_indep_tau h
  have hnn : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ τ i ω := by
    rw [ae_all_iff]
    intro i
    have h0 : μ {a | τ i a < 0} = 0 := by
      have : {a | τ i a < 0} = τ i ⁻¹' Set.Iio 0 := rfl
      rw [this, ← Measure.map_apply (hmeasτ i) measurableSet_Iio, (h.law_interarrival i).map_eq]
      exact Lv2Aux.expMeasure_Iio_zero _
    rw [ae_iff]
    simpa [not_le] using h0
  -- for each M, P(∀ i, τ i ≤ M) = 0
  have hM : ∀ M : ℕ, μ (⋂ i, τ i ⁻¹' Set.Iic (M : ℝ)) = 0 := by
    intro M
    set c := expMeasure (r : ℝ) (Set.Iic (M : ℝ)) with hc
    have hc1 : c < 1 := Lv2Aux.expMeasure_Iic_lt hr' M (by positivity)
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
