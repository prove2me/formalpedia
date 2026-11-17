-- Prove2me | solution 1 for simpleFunctionIntegralValue_map_ennreal_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:34:02.050208+00:00
-- url     : https://prove2.me/submissions/362bacbc-5c19-46cf-b649-a9817334f5dd

import Theorems.Thm_integralValue_map
import Theorems.Thm_ereal_coe_finset_sum__138bdd
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
    simpleFunctionIntegralValue μ (X.map fun x : ENNReal => (x : EReal)) =
      ((X.lintegral μ : ENNReal) : EReal) := by
  classical
  calc
    simpleFunctionIntegralValue μ (X.map fun x : ENNReal => (x : EReal))
        =
          ∑ x ∈ X.range,
            (x : EReal) * (μ (X ⁻¹' {x}) : EReal) := by
          simpa using
            integralValue_map μ (fun x : ENNReal => (x : EReal)) X
    _ =
        ((∑ x ∈ X.range, x * μ (X ⁻¹' {x}) : ENNReal) : EReal) := by
          rw [ereal_coe_finset_sum]
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact_mod_cast
            (show x * μ (X ⁻¹' {x}) = x * μ (X ⁻¹' {x}) from rfl)
    _ =
        ((X.lintegral μ : ENNReal) : EReal) := by
          rfl
