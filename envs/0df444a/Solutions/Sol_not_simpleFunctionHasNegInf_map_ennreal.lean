-- Prove2me | solution 1 for not_simpleFunctionHasNegInf_map_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:53:07.308017+00:00
-- url     : https://prove2.me/submissions/656bfe88-85ad-4ffc-86a6-91307f679d84

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    ¬ simpleFunctionHasNegInf μ (X.map fun x : ENNReal => (x : EReal)) := by
  classical
  rintro ⟨x, hx_range, hx_bot⟩
  -- it is the coercion of some `ENNReal`, hence nonnegative.
  have hx_nonneg : 0 ≤ x := by
    rcases SimpleFunc.mem_range.1 hx_range with ⟨a, rfl⟩
    change (0 : EReal) ≤ ((X a : ENNReal) : EReal)
    exact_mod_cast (show (0 : ENNReal) ≤ X a from zero_le)

  -- The measure factor is also nonnegative.
  have hμ_nonneg :
      0 ≤ ((μ ((X.map fun x : ENNReal => (x : EReal)) ⁻¹' {x}) : ENNReal) : EReal) := by
    positivity

  -- Hence the corresponding summand is nonnegative.
  have hterm_nonneg :
      0 ≤ simpleFunctionIntegralTerm μ
          (X.map fun x : ENNReal => (x : EReal)) x := by
    unfold simpleFunctionIntegralTerm
    exact mul_nonneg hx_nonneg hμ_nonneg

  -- But `⊥ < 0`, so a nonnegative term cannot be `⊥`.
  have hbot_lt_zero : (⊥ : EReal) < 0 := by
    exact EReal.bot_lt_coe 0

  have hnot : ¬ simpleFunctionIntegralTerm μ
          (X.map fun x : ENNReal => (x : EReal)) x ≤ ⊥ := by
    intro hle
    exact not_le_of_gt hbot_lt_zero (le_trans hterm_nonneg hle)

  exact hnot (le_of_eq hx_bot)
