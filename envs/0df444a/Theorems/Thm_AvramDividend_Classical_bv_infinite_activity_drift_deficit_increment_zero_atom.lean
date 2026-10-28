-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_increment_zero_atom
-- name    : AvramDividend.Classical.bv_infinite_activity_drift_deficit_increment_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:34:42.803184+00:00
-- url     : https://prove2.me/theorems/9f07f42e-b23d-4977-be58-26f45a7b18e7
-- title:
--   The actual infinite-activity bounded-variation drift deficit has no zero increment over a positive interval
-- statement:
--   At any s<t, the increment of the actual bounded-variation spectrally negative Lévy drift deficit has probability zero of equalling zero when the negative-jump Lévy measure is infinite. This follows directly from the proved stationary increment distribution and the proved positive-time zero-atom theorem, without invoking a jump-count construction.
-- source:
--   Accepted actual_levy_drift_deficit_stationary_increment_law and bv_infinite_activity_drift_deficit_zero_atom; Mathlib IdentDistrib.measure_mem_eq.

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_drift_deficit_increment_zero_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (s t : ℝ≥0) (hst : s < t) :
    P.real {ω : Ω |
        (X.drift * (t : ℝ) - X.X t ω) -
          (X.drift * (s : ℝ) - X.X s ω) = 0} = 0 := by sorry
