-- Prove2me | solution 1 for extension_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:08:56.15729+00:00
-- url     : https://prove2.me/submissions/d74b991e-92f6-4355-8a82-e04d29fb86f8

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_2_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_3_F000
import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_8_F000
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Tactic
import Theorems.Thm_thm_3_1


/-!
# Theorem 3.8: uniqueness of measure extension

The first theorem is the short Mathlib proof requested for the formalization.  The second
keeps the textbook route visible: on each finite cover piece it builds the equalizer
Dynkin system and explicitly applies the project's pi-lambda theorem `thm_3_7`.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ENNReal MeasurableSpace


universe u

theorem solution {X : Type u} (F₀ : FieldOfSets X) (pm : Premeasure F₀)
    (h_sigma_finite : IsSigmaFinite pm) :
    ∃! μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀.carrier pm.toSetFunction μ := by
  letI : MeasurableSpace X := MeasurableSpace.generateFrom F₀.carrier
  rcases thm_3_1 F₀ pm with ⟨μ, hμ⟩
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  rcases h_sigma_finite with ⟨A, hA, h_univ, hfinite⟩
  have hEq : ∀ s ∈ F₀.carrier, μ s = ν s := by
    intro s hs
    rw [hμ s hs, hν s hs]
  have hFinite : ∀ i, μ (A i) = ν (A i) ∧ μ (A i) < ⊤ := by
    intro i
    refine ⟨hEq _ (hA i), ?_⟩
    calc
      μ (A i) = pm.toSetFunction (A i) := hμ _ (hA i)
      _ = pm.μ₀ ⟨A i, hA i⟩ := pm.toSetFunction_of_mem (hA i)
      _ < ⊤ := hfinite i
  exact (thm_3_8 F₀.carrier rfl F₀.compl_mem
    (fun s hs t ht => F₀.union_mem s t hs ht)
    μ ν hEq A hA h_univ hFinite).symm