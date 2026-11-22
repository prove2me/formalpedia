-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_strict_lower_exit_no_creeping_ae_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_strict_lower_exit_no_creeping_ae_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:45:45.571563+00:00
-- url     : https://prove2.me/theorems/b24baa6b-514f-420d-86cc-3850386e89a9
-- title:
--   Standing-free BV strict lower exit has almost surely no creeping
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, the strict lower two-sided exit has almost surely no exact-boundary contact. The Standing hypothesis is replaced by the positive-root no-Standing capped-slope no-creeping child, retaining the proved dyadic capped-slope law.
-- source:
--   Adapted from exact accepted source of bv_strict_lower_exit_no_creeping_ae by replacing the Standing all-cap no-creeping import with its positive-root no-Standing counterpart.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_strict_lower_exit_no_creeping_ae_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) <
        ⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞) →
      x + X.X (⨅ (t : ℝ≥0) (_ : X.X t ω < -x),
        (t : ℝ≥0∞)).toNNReal ω ≠ 0 := by sorry
