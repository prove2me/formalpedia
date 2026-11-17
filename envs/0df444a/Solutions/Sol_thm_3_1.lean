-- Prove2me | solution 1 for thm_3_1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:03:37.290979+00:00
-- url     : https://prove2.me/submissions/b01746ac-458e-4fde-b2bb-5c4e5135b72f

import Theorems.Thm_Premeasure_toAddContent_isSigmaSubadditive
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F001
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_2_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic


/-!
# Carathéodory Extension Theorem: existence

The project's `Premeasure` is first exposed as Mathlib's `AddContent`.  Mathlib's
Carathéodory extension API then constructs the measure on the generated sigma-field.
Uniqueness is stated after Theorem 3.8, where the needed pi-lambda argument is available.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory ENNReal


universe u

theorem solution {X : Type u} (F₀ : FieldOfSets X) (pm : Premeasure F₀) :
    ∃ μ : @Measure X (MeasurableSpace.generateFrom F₀.carrier),
      IsExtension F₀.carrier pm.toSetFunction μ := by
  letI : MeasurableSpace X := MeasurableSpace.generateFrom F₀.carrier
  let μ : Measure X :=
    pm.toAddContent.measure F₀.isSetRing.isSetSemiring le_rfl
      pm.toAddContent_isSigmaSubadditive
  refine ⟨μ, ?_⟩
  intro s hs
  calc
    μ s = pm.toAddContent s :=
      AddContent.measure_eq pm.toAddContent F₀.isSetRing.isSetSemiring rfl
        pm.toAddContent_isSigmaSubadditive hs
    _ = pm.toSetFunction s := rfl