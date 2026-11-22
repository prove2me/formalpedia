-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T00:45:48.328275+00:00
-- url     : https://prove2.me/theorems/728b880d-e3d2-468b-8bb1-72e2ab895082
-- title:
--   Standing-free BV post-clock right germ from zero dyadic slopes
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, vanishing dyadic drift-deficit slopes after a clock imply a positive right germ after that clock. Standing is replaced by positive drift derived from the BV Laplace exponent bound at phi+1.
-- source:
--   Adapted from exact accepted source of bv_post_clock_positive_germ_of_dyadic_zero_ws01c by replacing bv_standing_drift_pos with a positive-root derivation using bv_laplace_exponent_le_drift_mul.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_post_clock_positive_germ_of_dyadic_zero_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation)
    (τ : Ω → ℝ≥0) (δ : ℕ → ℝ≥0)
    (hδpos : ∀ n, 0 < δ n)
    (hRatio : ∀ n, (δ n : ℝ) ≤ 2 * (δ (n + 1) : ℝ))
    (hCover : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → t < δ N →
      ∃ n : ℕ, N ≤ n ∧ δ (n + 1) ≤ t ∧ t ≤ δ n)
    (hSlope : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        (X.drift * (δ n : ℝ) -
          (X.X (τ ω + δ n) ω - X.X (τ ω) ω)) /
            (δ n : ℝ))
        atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂P,
      ∃ ε : ℝ≥0, 0 < ε ∧
        ∀ t : ℝ≥0, 0 < t → t < ε →
          0 < X.X (τ ω + t) ω - X.X (τ ω) ω := by sorry
