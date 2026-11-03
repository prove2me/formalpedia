-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_bv_ae_clipped_stopped_grid_local_lipschitz_from_interior_band
-- name    : AvramDividend.Classical.avram_wave6_06_actual_bv_ae_clipped_stopped_grid_local_lipschitz_from_interior_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:41:06.795206+00:00
-- url     : https://prove2.me/theorems/01748a98-8283-4ffa-91c6-717d9e00fa2c
-- title:
--   BV actual stopped source grid: a.e. positive interior localisation supplies timing Lipschitz band
-- statement:
--   For the actual spectrally negative Levy source X, dividend strategy D and min-clipped original ruin-localised grids, an almost-sure sample-path positive compact band containing every pre/postpayment grid reserve gives an almost-sure Lipschitz constant for w using the accepted BV C1 interior Lipschitz theorem. This constructs the exact hLocal premise of the accepted cofinal residual absorption, while explicitly exposing that it does not cover paths reaching or crossing zero.
-- source:
--   Avram, Palmowski, Pistorius Proposition 4(i), BV C1 source band; Proved Chat09 ebe807d7 and Chat06 timing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_finite_cap_local_C1_lipschitz
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_actual_bv_ae_clipped_stopped_grid_local_lipschitz_from_interior_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (w : ℝ → ℝ) (cap : ℝ)
    (hwC1 : X.BoundedVariation → ContDiffOn ℝ 1 w (Ioo 0 cap))
    (hInterior : ∀ᵐ ω ∂P, ∃ a b : ℝ,
      a < b ∧ Icc a b ⊆ Ioo 0 cap ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b)) :
    ∀ᵐ ω ∂P, ∃ L a b : ℝ,
      0 ≤ L ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        |w s - w t| ≤ L * |s - t|) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b) := by sorry
