-- Prove2me | solution 1 for levy_foundations_continuous_charFun_marginal_t
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:35.360549+00:00
-- url     : https://prove2.me/submissions/16dc551a-bb29-4aa7-9533-fe34b4ae8386

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent
import Definitions.Def_levy_foundations_levyExpFormula

open MeasureTheory Filter Topology
open scoped NNReal

namespace Lv2Aux

lemma map_sub_stationary {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : LevyFoundations.IsLevyProcess X μ) (s u : ℝ≥0) :
    μ.map (fun ω => X (s + u) ω - X s ω) = μ.map (X u) := by
  have := (h.stationary_increments s u).map_eq
  have h0 := h.start_zero
  have e : LevyFoundations.increment X 0 u = X u := by
    funext ω; simp [LevyFoundations.increment, h0]
  have e' : LevyFoundations.increment X s (s + u) = fun ω => X (s + u) ω - X s ω := rfl
  rwa [e, e'] at this

lemma charFun_add {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (s u : ℝ≥0) (ξ : E) :
    charFun (μ.map (X (s + u))) ξ = charFun (μ.map (X s)) ξ * charFun (μ.map (X u)) ξ := by
  have hind := h.indep_increments.indepFun_sub_sub (r := 0) (s := s) (t := s + u)
    zero_le le_self_add
  have h0 := h.start_zero
  have e1 : (X s - X 0) = X s := by funext ω; simp [h0]
  rw [e1] at hind
  have e2 : (X s + (X (s + u) - X s)) = X (s + u) := by funext ω; simp
  have := ProbabilityTheory.IndepFun.charFun_map_add_eq_mul (hX s).aemeasurable
    (((hX (s + u)).sub (hX s)).aemeasurable) hind
  rw [e2] at this
  rw [congrFun this ξ, Pi.mul_apply]
  congr 2
  exact map_sub_stationary h s u


lemma charFun_zero_time {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ) (ξ : E) :
    charFun (μ.map (X 0)) ξ = 1 := by
  have h0 := h.start_zero
  simp [h0, Measure.map_const, charFun_apply]

lemma tendsto_charFun_zero {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (ξ : E) :
    Tendsto (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) (𝓝 0) (𝓝 1) := by
  have hrep : ∀ t : ℝ≥0, charFun (μ.map (X t)) ξ =
      ∫ ω, Complex.exp ((inner ℝ (X t ω) ξ : ℝ) * Complex.I) ∂μ := by
    intro t
    rw [charFun_apply, integral_map (hX t).aemeasurable (by fun_prop)]
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 (0 : ℝ≥0))
    (F := fun (t : ℝ≥0) ω => Complex.exp ((inner ℝ (X t ω) ξ : ℝ) * Complex.I))
    (f := fun ω => Complex.exp ((inner ℝ (X 0 ω) ξ : ℝ) * Complex.I)) (fun _ => 1)
    (Filter.Eventually.of_forall fun t => by
      exact (by have := hX t; fun_prop : Measurable fun ω => Complex.exp ((inner ℝ (X t ω) ξ : ℝ) * Complex.I)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun ω => by
      simp [Complex.norm_exp_ofReal_mul_I])
    (integrable_const _) ?_
  · have h1 : charFun (μ.map (X 0)) ξ = 1 := charFun_zero_time h ξ
    have h2 : (∫ ω, Complex.exp ((inner ℝ (X 0 ω) ξ : ℝ) * Complex.I) ∂μ) = 1 := by
      rw [← hrep 0, h1]
    rw [h2] at hlim
    simpa only [hrep] using hlim
  · filter_upwards [h.cadlag_ae] with ω hω
    have h0 := hω 0
    have hc : ContinuousAt (fun t : ℝ≥0 => X t ω) 0 := by
      have := h0.1
      have hI : Set.Ici (0 : ℝ≥0) = Set.univ := by ext x; simp
      rwa [hI, continuousWithinAt_univ] at this
    exact ((by fun_prop : Continuous fun x : E => Complex.exp ((inner ℝ x ξ : ℝ) * Complex.I)).continuousAt.comp hc).tendsto


end Lv2Aux

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t))
    (ξ : E) :
    Continuous (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) := by
  set φ : ℝ≥0 → ℂ := fun t => charFun (μ.map (X t)) ξ with hφ
  have hφ0 : φ 0 = 1 := Lv2Aux.charFun_zero_time h ξ
  have hφadd : ∀ s u, φ (s + u) = φ s * φ u := fun s u => Lv2Aux.charFun_add h hX s u ξ
  have hφle : ∀ t, ‖φ t‖ ≤ 1 := by
    intro t
    have : IsProbabilityMeasure (μ.map (X t)) := Measure.isProbabilityMeasure_map (hX t).aemeasurable
    exact norm_charFun_le_one ξ
  have hφtend : Tendsto φ (𝓝 0) (𝓝 1) := Lv2Aux.tendsto_charFun_zero h hX ξ
  have hsub : ∀ t0 : ℝ≥0, Tendsto (fun s : ℝ≥0 => ‖φ (s - t0) - 1‖ + ‖φ (t0 - s) - 1‖)
      (𝓝 t0) (𝓝 0) := by
    intro t0
    have h1 : Tendsto (fun s : ℝ≥0 => s - t0) (𝓝 t0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ≥0 => s - t0) := continuous_id.sub continuous_const
      simpa using hc.tendsto t0
    have h2 : Tendsto (fun s : ℝ≥0 => t0 - s) (𝓝 t0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ≥0 => t0 - s) := continuous_const.sub continuous_id
      simpa using hc.tendsto t0
    have h3 : ∀ {g : ℝ≥0 → ℝ≥0}, Tendsto g (𝓝 t0) (𝓝 0) →
        Tendsto (fun s => ‖φ (g s) - 1‖) (𝓝 t0) (𝓝 0) := by
      intro g hg
      have := ((hφtend.comp hg).sub_const 1).norm
      simpa using this
    simpa using (h3 h1).add (h3 h2)
  refine continuous_iff_continuousAt.2 fun t0 => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) (hsub t0)
  rcases le_total t0 s with hs | hs
  · have e : φ s = φ t0 * φ (s - t0) := by
      rw [← hφadd, add_tsub_cancel_of_le hs]
    have e2 : t0 - s = 0 := tsub_eq_zero_of_le hs
    rw [e2, hφ0, sub_self, norm_zero, add_zero]
    calc ‖φ s - φ t0‖ = ‖φ t0‖ * ‖φ (s - t0) - 1‖ := by
          rw [← norm_mul]; congr 1; rw [e]; ring
      _ ≤ 1 * ‖φ (s - t0) - 1‖ := mul_le_mul_of_nonneg_right (hφle t0) (norm_nonneg _)
      _ = _ := one_mul _
  · have e : φ t0 = φ s * φ (t0 - s) := by
      rw [← hφadd, add_tsub_cancel_of_le hs]
    have e2 : s - t0 = 0 := tsub_eq_zero_of_le hs
    rw [e2, hφ0, sub_self, norm_zero, zero_add]
    calc ‖φ s - φ t0‖ = ‖φ t0 - φ s‖ := norm_sub_rev _ _
      _ = ‖φ s‖ * ‖φ (t0 - s) - 1‖ := by
          rw [← norm_mul]; congr 1; rw [e]; ring
      _ ≤ 1 * ‖φ (t0 - s) - 1‖ := mul_le_mul_of_nonneg_right (hφle s) (norm_nonneg _)
      _ = _ := one_mul _
