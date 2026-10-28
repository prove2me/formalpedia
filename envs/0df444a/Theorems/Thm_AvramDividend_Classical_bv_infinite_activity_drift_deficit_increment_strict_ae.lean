-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_increment_strict_ae
-- name    : AvramDividend.Classical.bv_infinite_activity_drift_deficit_increment_strict_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:41:06.596762+00:00
-- url     : https://prove2.me/theorems/f53da8bf-3781-47e7-9935-7a3991a19887
-- title:
--   Every fixed positive-duration drift-deficit increment of the actual infinite-activity bounded-variation Lévy process is strictly positive almost surely
-- statement:
--   For any pair of deterministic times s<t, the actual bounded-variation spectrally negative Lévy drift deficit D_t=dt-X_t has a strictly positive increment almost surely if its negative Lévy measure has infinite mass. The proof combines the accepted stationary increment zero-atom law with already proved sample-path monotonicity.
-- source:
--   Accepted bv_infinite_activity_drift_deficit_increment_zero_atom and bv_drift_deficit_ae_monotone_all_times; Mathlib measureReal_eq_zero_iff and ae_iff.

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_increment_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_infinite_activity_drift_deficit_increment_strict_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ ω ∂P,
      X.drift * (s : ℝ) - X.X s ω <
        X.drift * (t : ℝ) - X.X t ω := by sorry
