-- Prove2me | solution 1 for levy_foundations_pieceCountEventProb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:42:55.288059+00:00
-- url     : https://prove2.me/submissions/9aa729c2-693c-4c7d-85cb-b9678db64358

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Definitions.Def_levy_foundations_isPoissonPointFamily

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (k j : ℕ) :
    μ.real {ω | K k ω = j} =
      (poissonMeasure (m (LevyFoundations.prmPiece m k)).toNNReal).real {j} := by
  have h1 : μ {ω | K k ω = j} =
      poissonMeasure (m (LevyFoundations.prmPiece m k)).toNNReal {j} := by
    rw [show {ω | K k ω = j} = K k ⁻¹' {j} from rfl,
      ← Measure.map_apply (hd.measurable_count k) (measurableSet_singleton j),
      (hd.law_count k).map_eq]
  rw [measureReal_def, h1, ← measureReal_def]
