-- Prove2me | solution 1 for levy_foundations_prmFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:18:32.115794+00:00
-- url     : https://prove2.me/submissions/0dd0b582-e2b4-444b-9704-c2c08471465e

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Definitions.Def_levy_foundations_prmPiece

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    {E : Type*} [MeasurableSpace E] (m : Measure E)
    [SigmaFinite m] (k : ℕ) :
    m (LevyFoundations.prmPiece m k) < ⊤ := by
  change m (disjointed (spanningSets m) k) < ⊤
  exact lt_of_le_of_lt
    (measure_mono (disjointed_subset (spanningSets m) k))
    (measure_spanningSets_lt_top m k)
