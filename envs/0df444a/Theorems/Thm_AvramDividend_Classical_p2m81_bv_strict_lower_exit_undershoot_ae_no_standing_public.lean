-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_strict_lower_exit_undershoot_ae_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_strict_lower_exit_undershoot_ae_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:45:53.687797+00:00
-- url     : https://prove2.me/theorems/512aa2e0-1c93-4cb4-94ae-368541d85a64
-- title:
--   Standing-free BV strict lower exit has a negative undershoot almost surely
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, the strict lower two-sided exit has a genuinely negative realised reserve almost surely. The Standing hypothesis is replaced by the positive-root no-Standing no-creeping child.
-- source:
--   Adapted from exact accepted source of bv_strict_lower_exit_undershoot_ae_ws01c by replacing the Standing no-creeping import with its positive-root no-Standing counterpart.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_strict_lower_exit_undershoot_ae_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω < 0 := by sorry
