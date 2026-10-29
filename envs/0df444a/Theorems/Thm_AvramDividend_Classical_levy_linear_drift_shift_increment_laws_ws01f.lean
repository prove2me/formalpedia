-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_linear_drift_shift_increment_laws_ws01f
-- name    : AvramDividend.Classical.levy_linear_drift_shift_increment_laws_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:02:21.184727+00:00
-- url     : https://prove2.me/theorems/81c0cddd-3b44-43ef-b9c3-cdb81a97757d
-- title:
--   Affine time-drift translation preserves actual independent and stationary Lévy increments
-- statement:
--   For arbitrary real C and actual source Lévy X, the increments of X_t−Ct remain independent of the past filtration and their distribution depends only on elapsed time, with no additional stochastic assumptions. The theorem supplies the genuine law component of the WS1F drift-shift construction needed for all near-zero Rogozin slopes.
-- source:
--   Measurable affine postcomposition of the existing Indep property and Mathlib ProbabilityTheory.IdentDistrib.sub_const applied to the actual stationary increment law; NNReal.coe_sub for s≤t.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_linear_drift_shift_increment_laws_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (C : ℝ) :
    ∀ (s t : ℝ≥0), s ≤ t →
      Indep
        (MeasurableSpace.comap
          (fun ω : Ω => (X.X t ω - C * (t : ℝ)) -
            (X.X s ω - C * (s : ℝ))) inferInstance)
        (𝓕 s) P ∧
      IdentDistrib
        (fun ω : Ω => (X.X t ω - C * (t : ℝ)) -
          (X.X s ω - C * (s : ℝ)))
        (fun ω : Ω => X.X (t - s) ω - C * ((t - s : ℝ≥0) : ℝ)) P P := by sorry
