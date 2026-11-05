-- Prove2me | solution 1 for levy_foundations_isInfinitelyDivisible_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:30.972254+00:00
-- url     : https://prove2.me/submissions/bbb2c747-905f-4e9a-8a96-151503e53c0b

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal Nat

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

lemma map_add_law {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (s u : ℝ≥0) :
    μ.map (X (s + u)) = (μ.map (X s)) ∗ (μ.map (X u)) := by
  have hind := h.indep_increments.indepFun_sub_sub (r := 0) (s := s) (t := s + u)
    zero_le le_self_add
  have h0 := h.start_zero
  have e1 : (X s - X 0) = X s := by funext ω; simp [h0]
  rw [e1] at hind
  have e2 : (X s + (X (s + u) - X s)) = X (s + u) := by funext ω; simp
  have := IndepFun.map_add_eq_map_conv_map₀ (hX s).aemeasurable
    (((hX (s + u)).sub (hX s)).aemeasurable) hind
  rw [e2] at this
  rw [this]
  congr 1
  exact map_sub_stationary h s u

end Lv2Aux

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    LevyFoundations.isInfinitelyDivisibleLaw (μ.map (X t)) := by
  intro n hn
  set s : ℝ≥0 := t / n with hs
  have hν : IsProbabilityMeasure (μ.map (X s)) := isProbabilityMeasure_map (hX s).aemeasurable
  refine ⟨μ.map (X s), hν, ?_⟩
  have key : ∀ k : ℕ, μ.map (X (k * s)) = LevyFoundations.iteratedConvolutionPower (μ.map (X s)) k := by
    intro k
    induction k with
    | zero =>
      have h0 := h.start_zero
      simp [h0, Measure.map_const, LevyFoundations.iteratedConvolutionPower]
    | succ k ih =>
      have e : ((k + 1 : ℕ) : ℝ≥0) * s = s + k * s := by push_cast; ring
      rw [e, Lv2Aux.map_add_law h hX, ih]
      rfl
  have := key n
  have e : (n : ℝ≥0) * s = t := by
    rw [hs]; field_simp
  rwa [e] at this
