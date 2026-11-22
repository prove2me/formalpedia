-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_actual_raw_clock_positive_germ_of_cap_slopes_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_actual_raw_clock_positive_germ_of_cap_slopes_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:45:45.455971+00:00
-- url     : https://prove2.me/theorems/c6ded12a-8976-44a2-8494-84762ce4e194
-- title:
--   Standing-free BV capped-slope germs transfer to the raw clock
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, positive right germs at every finite capped stopping clock imply the corresponding germ at the raw stopping clock.
-- source:
--   Adapted from exact accepted source of bv_actual_raw_clock_positive_germ_of_cap_slopes_ws01c by replacing the Standing post-clock germ with the no-Standing positive-root child.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_actual_raw_clock_positive_germ_of_cap_slopes_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation)
    (τ : Ω → ℝ≥0∞) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hCapSlope : ∀ N : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal + δ n) ω -
            X.X ((τ ω ⊓ (N : ℝ≥0∞)).toNNReal) ω)) /
          (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      τ ω < ⊤ →
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, 0 < t → t < ε →
          0 < X.X ((τ ω).toNNReal + t) ω -
            X.X ((τ ω).toNNReal) ω := by sorry
