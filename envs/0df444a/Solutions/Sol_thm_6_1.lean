-- Prove2me | solution 1 for thm_6_1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:48:15.400284+00:00
-- url     : https://prove2.me/submissions/9abe203e-b1e8-4368-8690-4037c57c5009

import Theorems.Thm_Thm61Support_integralValue_const_mul_real_of_defined
import Theorems.Thm_Thm61Support_integralValue_add_of_cellwise_distrib
import Theorems.Thm_integralValue_mono_fun
import Theorems.Thm_def62_eq_some_iff
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Thm61Support

end Thm61Support

theorem solution (μ : Measure Ω) (X Y : SimpleFunc Ω EReal) (α : ℝ) :
    (∀ {x xα : EReal},
        def_6_2 μ X = some x →
        def_6_2 μ (X.map fun t => (α : EReal) * t) = some xα →
        xα = (α : EReal) * x) ∧
      (∀ {x y xy : EReal},
        def_6_2 μ X = some x →
        def_6_2 μ Y = some y →
        simpleFunctionIntegralAdd μ X Y = some xy →
        xy = x + y) ∧
      (X ≤ Y →
        ∀ {x y : EReal},
          def_6_2 μ X = some x →
          def_6_2 μ Y = some y →
          x ≤ y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x xα hX hαX
    rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hX with ⟨hXdef, hx⟩
    rcases
      (def62_eq_some_iff (μ := μ) (f := X.map fun t => (α : EReal) * t) (v := xα)).1 hαX with
      ⟨_, hxα⟩
    rw [← hxα,
      Thm61Support.integralValue_const_mul_real_of_defined
        (μ := μ) (X := X) (α := α) hXdef,
      hx]
  · intro x y xy hX hY hXY
    unfold simpleFunctionIntegralAdd at hXY
    split_ifs at hXY with hcell
    · rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hX with ⟨_, hx⟩
      rcases (def62_eq_some_iff (μ := μ) (f := Y) (v := y)).1 hY with ⟨_, hy⟩
      rcases (def62_eq_some_iff (μ := μ) (f := X + Y) (v := xy)).1 hXY with ⟨_, hxy⟩
      rw [← hxy,
        Thm61Support.integralValue_add_of_cellwise_distrib (μ := μ) (X := X) (Y := Y) hcell,
        hx, hy]
  · intro hXY x y hX hY
    rcases (def62_eq_some_iff (μ := μ) (f := X) (v := x)).1 hX with ⟨_, hx⟩
    rcases (def62_eq_some_iff (μ := μ) (f := Y) (v := y)).1 hY with ⟨_, hy⟩
    rw [← hx, ← hy]
    exact integralValue_mono_fun (μ := μ) hXY
