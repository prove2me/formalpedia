-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_lower_first_capped_terminal_scale_zero_ae_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_lower_first_capped_terminal_scale_zero_ae_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T00:45:47.493087+00:00
-- url     : https://prove2.me/theorems/48de8eba-b852-44e9-b5ed-9349673b6ef1
-- title:
--   Standing-free capped lower-first stopped q-scale vanishes
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, the discounted stopped q-scale vanishes almost surely on lower-first exit before the finite cap. Standing is replaced by the no-Standing undershoot child.
-- source:
--   Adapted from exact accepted source of avram_ws01b_bv_lower_first_capped_terminal_scale_zero_ae by replacing the Standing undershoot import with its positive-root no-Standing counterpart.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_lower_first_capped_terminal_scale_zero_ae_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω →
      (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T →
      Real.exp (-(q * ((min
        (min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
      W (x + X.X (min
        (min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω) = 0 := by sorry
