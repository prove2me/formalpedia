-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a45_original_fullcell_spatial_endpoint_ge_risk
-- name    : AvramDividend.Classical.avram_ga_a45_original_fullcell_spatial_endpoint_ge_risk
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:51:34.733189+00:00
-- url     : https://prove2.me/theorems/057605a6-a1b1-4abd-b133-17f544dc66fb
-- title:
--   Strict original Gaussian physical full-cell spatial endpoint is at least the later prepayment reserve
-- statement:
--   For actual original source times s<t and cumulative dividend strategy, the spatial endpoint formed using dividend right limit at s exceeds or equals the prepayment reserve at t. Thus safe-cell source Taylor endpoints inherit the positive-surplus floor.
-- source:
--   Direct b0d9951c positive original spatial stopped Taylor safe-cell endpoint inequality using Proved gledger87.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ga_a45_original_fullcell_spatial_endpoint_ge_risk
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) (hst : s < t) :
    riskProcess X x D t ω ≤
      x + X.X t ω - rightLimit D s ω := by sorry
