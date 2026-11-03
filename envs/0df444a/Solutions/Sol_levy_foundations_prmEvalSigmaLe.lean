-- Prove2me | solution 1 for levy_foundations_prmEvalSigmaLe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:40:46.771027+00:00
-- url     : https://prove2.me/submissions/2f2d6571-39cc-42c2-88f0-e2a71b0b7a64

import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_levy_foundations_prmEvalSigma
import Theorems.Thm_levy_foundations_measurablePRMEval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) (R : Set E)
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) :
    LevyFoundations.prmEvalSigma K X m R ≤
      (inferInstance : MeasurableSpace Ω) := by
  unfold LevyFoundations.prmEvalSigma
  exact iSup_le fun B =>
    (levy_foundations_measurablePRMEval K X hK hX B.2.1).comap_le
