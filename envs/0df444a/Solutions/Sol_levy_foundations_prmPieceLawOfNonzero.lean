-- Prove2me | solution 1 for levy_foundations_prmPieceLawOfNonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:08:06.790978+00:00
-- url     : https://prove2.me/submissions/02275b77-ed5c-4ba2-acf4-a22c2dca3c34

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Definitions.Def_levy_foundations_prmPiece
import Definitions.Def_levy_foundations_prmPieceLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (k : ℕ)
    (hk : m (LevyFoundations.prmPiece m k) ≠ 0) :
    LevyFoundations.prmPieceLaw m k =
      (m (LevyFoundations.prmPiece m k))⁻¹ •
        m.restrict (LevyFoundations.prmPiece m k) := by
  unfold LevyFoundations.prmPieceLaw
  rw [if_neg hk]
