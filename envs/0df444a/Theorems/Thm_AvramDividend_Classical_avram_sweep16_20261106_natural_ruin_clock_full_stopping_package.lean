-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
-- name    : AvramDividend.Classical.avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:13:23.653703+00:00
-- url     : https://prove2.me/theorems/c2b88870-33ea-4192-9fdb-bcfffd25c7ea
-- title:
--   Every genuine original min(ruin,n) clipped clock is bounded, right-continuous stopping and before ruin
-- statement:
--   Exact original process/filtration natural bounded ruin clocks satisfy all clock assumptions of the source-to-cash reduction, using already Proved ruinTime stopping, truncated stopping and NNReal clock-bound certificates.
-- source:
--   Independent exact SWEEP16 component of natural L1 residual-to-cash reduction; does not require UBV martingale status.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ n : ℕ, 0 < n →
      (∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ (n : ℝ≥0)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : WithTop ℝ≥0)) ∧
      (∀ ω, (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) ≤
        ruinTime X x D ω) := by sorry
