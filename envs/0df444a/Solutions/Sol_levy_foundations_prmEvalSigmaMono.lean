-- Prove2me | solution 1 for levy_foundations_prmEvalSigmaMono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:22:32.398997+00:00
-- url     : https://prove2.me/submissions/9f4758d8-0085-4ab0-a508-640b493a8ae7

import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_levy_foundations_prmEvalSigma

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) {R S : Set E} (hRS : R ⊆ S) :
    LevyFoundations.prmEvalSigma K X m R ≤
      LevyFoundations.prmEvalSigma K X m S := by
  unfold LevyFoundations.prmEvalSigma
  exact iSup_le fun B =>
    le_iSup_of_le
      (⟨B.1, B.2.1, B.2.2.1.trans hRS, B.2.2.2⟩ :
        LevyFoundations.prmEvalIndex m S)
      le_rfl
