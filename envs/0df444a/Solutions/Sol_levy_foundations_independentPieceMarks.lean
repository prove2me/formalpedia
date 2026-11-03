-- Prove2me | solution 1 for levy_foundations_independentPieceMarks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:33:28.195758+00:00
-- url     : https://prove2.me/submissions/7ec6d055-aa14-4c4b-8586-59c8cc9a4bad

import Mathlib.Probability.Independence.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k : ℕ) :
    iIndepFun (fun n => X k n) μ := by
  have h := hd.indep.precomp (g := fun n => Sum.inr (k, n))
    (fun a b hab => by simpa using hab)
  exact h
