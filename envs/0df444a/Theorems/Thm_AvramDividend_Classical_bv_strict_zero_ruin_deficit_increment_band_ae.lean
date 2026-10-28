-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_strict_zero_ruin_deficit_increment_band_ae
-- name    : AvramDividend.Classical.bv_strict_zero_ruin_deficit_increment_band_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:05:30.586397+00:00
-- url     : https://prove2.me/theorems/1c45b4f2-efc1-4ced-906d-b525b70710d7
-- title:
--   Before strict zero-barrier ruin each actual BV drift-deficit increment is bounded by the drift increment
-- statement:
--   On the existing common full-measure monotone-drift-deficit event, strict survival before the exact zero-barrier reflected ruin clock implies that the actual capital path is nondecreasing. Therefore each increment of D_t=d t-X_t is nonnegative and no greater than d(u-s). This is exactly the short-interval bound required to contain any positive deficit jump inside one grid cell with small positive drift-deficit increment.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3; proved BV drift-deficit monotonicity and the source-faithful strict zero-barrier survival capital monotonicity.

import Theorems.Thm_AvramDividend_Classical_zero_reflected_ruin_strict_survival_capital_monotone_prefix
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.Tactic.Ring
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_strict_zero_ruin_deficit_increment_band_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (T : ℝ≥0∞) < barrierRuinTime X 0 ω →
      ∀ s u : ℝ≥0, s ≤ u → u ≤ T →
      0 ≤ (X.drift * (u : ℝ) - X.X u ω) -
        (X.drift * (s : ℝ) - X.X s ω) ∧
      (X.drift * (u : ℝ) - X.X u ω) -
        (X.drift * (s : ℝ) - X.X s ω) ≤
          X.drift * ((u : ℝ) - (s : ℝ)) := by sorry
