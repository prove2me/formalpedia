-- Prove2me | solution 1 for levy_foundations_prmEvalSigmaApplyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:22:44.521494+00:00
-- url     : https://prove2.me/submissions/54698ffc-b899-4c71-97da-05e4c84dbbc9

import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_levy_foundations_prmEvalSigma
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) {B R : Set E}
    (hB : MeasurableSet B) (hBR : B ⊆ R)
    (hfin : m B < ⊤) :
    Measurable[LevyFoundations.prmEvalSigma K X m R]
      (fun ω => LevyFoundations.poissonRandomMeasure K X ω B) := by
  unfold LevyFoundations.prmEvalSigma
  exact Measurable.of_comap_le <|
    le_iSup
      (fun B' : LevyFoundations.prmEvalIndex m R =>
        MeasurableSpace.comap
          (fun ω => LevyFoundations.poissonRandomMeasure K X ω B'.1)
          inferInstance)
      ⟨B, hB, hBR, hfin⟩
