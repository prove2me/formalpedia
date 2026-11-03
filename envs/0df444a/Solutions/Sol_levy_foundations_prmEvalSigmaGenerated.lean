-- Prove2me | solution 1 for levy_foundations_prmEvalSigmaGenerated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:23:09.768456+00:00
-- url     : https://prove2.me/submissions/8294a96b-81e0-492f-8bd4-a61e3018fb65

import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_levy_foundations_prmEvalPiSystem
import Definitions.Def_levy_foundations_prmEvalSigma
import Mathlib.MeasureTheory.MeasurableSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) (R : Set E) :
    LevyFoundations.prmEvalSigma K X m R =
      MeasurableSpace.generateFrom
        (LevyFoundations.prmEvalPiSystem K X m R) := by
  show (⨆ B : LevyFoundations.prmEvalIndex m R,
      MeasurableSpace.comap
        (fun ω => LevyFoundations.poissonRandomMeasure K X ω B.1)
        inferInstance) =
    MeasurableSpace.generateFrom
      (LevyFoundations.prmEvalPiSystem K X m R)
  rw [LevyFoundations.prmEvalPiSystem,
    generateFrom_piiUnionInter_measurableSet
      (fun B : LevyFoundations.prmEvalIndex m R =>
        MeasurableSpace.comap
          (fun ω => LevyFoundations.poissonRandomMeasure K X ω B.1)
          inferInstance)
      Set.univ,
    iSup_univ]
