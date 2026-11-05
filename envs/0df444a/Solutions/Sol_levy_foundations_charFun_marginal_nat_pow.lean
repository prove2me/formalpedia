-- Prove2me | solution 1 for levy_foundations_charFun_marginal_nat_pow
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:58:31.763806+00:00
-- url     : https://prove2.me/submissions/c99fa2dd-48a6-4ead-996a-d6d2b8d53f44

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
  have := IndepFun.charFun_map_add_eq_mul (hX s).aemeasurable
    (((hX (s + u)).sub (hX s)).aemeasurable) hind
  rw [e2] at this
  rw [congrFun this ξ, Pi.mul_apply]
  congr 2
  exact map_sub_stationary h s u

end Lv2Aux

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (n : ℕ) (ξ : E) :
    charFun (μ.map (X (n : ℝ≥0))) ξ =
      (charFun (μ.map (X 1)) ξ) ^ n := by
  induction n with
  | zero =>
    have h0 := h.start_zero
    simp [h0, Measure.map_const, charFun_apply]
  | succ n ih =>
    have := Lv2Aux.charFun_add h hX (n : ℝ≥0) 1 ξ
    rw [Nat.cast_succ, this, ih, pow_succ]
