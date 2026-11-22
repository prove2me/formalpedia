-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_strict_lower_exit_no_creeping_of_cap_slopes_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_strict_lower_exit_no_creeping_of_cap_slopes_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:45:44.976334+00:00
-- url     : https://prove2.me/theorems/1b578d91-a670-4324-a7a5-41eaeec31e19
-- title:
--   Standing-free BV no-creeping from capped-slope germs
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, vanishing drift-deficit slopes at all finite capped lower-exit clocks imply almost surely that the strict lower exit does not land exactly on the boundary.
-- source:
--   Adapted from exact accepted source of bv_strict_lower_exit_no_creeping_ae by replacing Standing with the no-Standing raw-clock germ child and its positive-root parameters.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_strict_lower_exit_no_creeping_of_cap_slopes_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hCapSlope : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X (((twoSidedExitDownTime X (-x) ω) ⊓
              (N : ℝ≥0∞)).toNNReal + δ n) ω -
            X.X (((twoSidedExitDownTime X (-x) ω) ⊓
              (N : ℝ≥0∞)).toNNReal) ω)) /
          (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω →
      x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω ≠ 0 := by sorry
