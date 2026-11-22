-- Prove2me | solution 1 for iteration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:48.413951+00:00
-- url     : https://prove2.me/submissions/a7a95082-03cc-45b7-acd7-eb71b44dd04b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_LocalLemma
import Theorems.Thm_IndividualBound_compl

set_option autoImplicit true
open MeasureTheory ProbabilityTheory Measure
variable {ι Ω : Type*} {hΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {A : ι → Set Ω} {N : ι → Finset ι} {x : ι → ℝ} {i j : ι} {S T : Finset ι}
open Finset
theorem _root_.solution [DecidableEq ι] [IsProbabilityMeasure P] (hA : ∀ i, MeasurableSet (A i))
    {t t' : Finset ι} (ht : Disjoint t t')
    (hx₁ : ∀ i, x i ≤ 1)
    (S : Finset ι)
    (htS : t ⊆ S)
    (ht'S : t' ⊆ S)
    (h : ∀ T ⊂ S, ∀ {i}, i ∉ T → IndividualBound P A x i T) :
    (∏ j ∈ t, (1 - x j)) * P.real (⋂ j ∈ t', (A j)ᶜ) ≤ P.real (⋂ j ∈ t ∪ t', (A j)ᶜ) := by
  induction t using cons_induction_on with
  | empty => simp
  | cons a t hat ih =>
    replace ⟨hat', htt⟩ : a ∉ t' ∧ Disjoint t t' := by simpa using ht
    simp only [cons_eq_insert] at htS
    suffices ((1 - x a) * ∏ j ∈ t, (1 - x j)) * P.real (⋂ j ∈ t', (A j)ᶜ) ≤
        P.real ((A a)ᶜ ∩ (⋂ x ∈ t ∪ t', (A x)ᶜ)) by simpa [- mem_union, hat] using this
    calc
      _ = (1 - x a) * ((∏ j ∈ t, (1 - x j)) * P.real (⋂ j ∈ t', (A j)ᶜ)) := by ring
      _ ≤ (1 - x a) * P.real (⋂ j ∈ t ∪ t', (A j)ᶜ) := by
        gcongr
        · simp [hx₁]
        · apply ih htt ((subset_insert _ _).trans htS)
      _ ≤ _ := by
        have ha : a ∉ t ∪ t' := by simp [hat, hat']
        have : insert a (t ∪ t') ⊆ S := by
          simpa [insert_subset_iff, union_subset_iff, ht'S] using htS
        exact (h _ (Finset.ssubset_of_ssubset_of_subset (ssubset_insert ha) this) ha).compl (hA _)
