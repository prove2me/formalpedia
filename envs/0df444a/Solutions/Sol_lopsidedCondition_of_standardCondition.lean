-- Prove2me | solution 1 for lopsidedCondition_of_standardCondition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:38:57.308737+00:00
-- url     : https://prove2.me/submissions/a1c473a1-e31d-4828-a4ce-f6dfb68984a7

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_IndepFrom_prob_inter_biInter

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
theorem _root_.solution [IsProbabilityMeasure P]
    (h : standardCondition P A N) :
    lopsidedCondition P A N := by
  intro i S hiS hS
  specialize h i
  simp only [← Finset.mem_coe (s := S)]
  rw [h.prob_inter_biInter (C := (S : Set ι)) (A := fun i ↦ (A i)ᶜ) S.countable_toSet _]
  intro j hj
  simp only [Finset.mem_coe] at hj
  right
  simp only [compl_compl]
  rw [Finset.disjoint_right] at hS
  apply Set.mem_image_of_mem
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Finset.mem_coe] -- TODO: try removing the simp
  grind
