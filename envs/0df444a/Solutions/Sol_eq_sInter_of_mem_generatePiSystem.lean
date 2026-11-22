-- Prove2me | solution 1 for eq_sInter_of_mem_generatePiSystem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:02.943172+00:00
-- url     : https://prove2.me/submissions/3b2cc659-d73c-489c-a2fb-fbbb90b86acf

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution {Ω : Type*} {t : Set (Set Ω)} {A : Set Ω}
    (hA : A ∈ generatePiSystem t) :
    ∃ S : Set (Set Ω), S ⊆ t ∧ A = ⋂₀ S := by
  induction hA with
  | @base s hs =>
    refine ⟨{s}, by simpa, by simp⟩
  | @inter s₁ s₂ _ _ h hs₁ hs₂ =>
    obtain ⟨S₁, hS₁, rfl⟩ := hs₁
    obtain ⟨S₂, hS₂, rfl⟩ := hs₂
    refine ⟨S₁ ∪ S₂, Set.union_subset hS₁ hS₂, by simp [Set.sInter_union]⟩
