-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_stopped_min_away_zero_ae_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_stopped_min_away_zero_ae_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:45:52.526198+00:00
-- url     : https://prove2.me/theorems/40254e6a-2e4b-46f5-975f-20fdc7a69b68
-- title:
--   Standing-free BV stopped two-sided reserve avoids zero almost surely
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, the realised reserve at the finite two-sided exit is almost surely nonzero. The Standing hypothesis is replaced by the positive-root no-Standing undershoot child.
-- source:
--   Adapted from exact accepted source of avram_ws01b_bv_stopped_min_away_zero_ae by replacing the Standing undershoot import with its positive-root no-Standing counterpart.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_stopped_min_away_zero_ae_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      x + X.X (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)).toNNReal ω ≠ 0 := by sorry
