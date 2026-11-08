-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_ruin_clock_uniform_mesh_small_ae
-- name    : AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_uniform_mesh_small_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:34:11.53785+00:00
-- url     : https://prove2.me/theorems/49cdc731-a2a1-4bfe-8e7c-0ee7e9998f4d
-- title:
--   Original bounded-variation Levy compensated ruin-stopped increments vanish uniformly on physical grids
-- statement:
--   On a common almost-sure event, the exact original bounded-variation spectrally negative Levy process plus its actual negative-jump sum has uniformly vanishing increments along a physically uniform grid clipped by the original dividend-dependent ruinTime capped at S. The explicit bound is absolute drift times physical cell width, and holds at every index and every finite n. This keeps the original process, stopping clock, and jump convention intact. It does not assert the generator-integrability or localised Taylor convergence obligations.
-- source:
--   AVRAM BV-RESIDUAL10 round 8, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_uniform_stopped_cell_width_bound

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_uniform_mesh_small_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (S : ℝ≥0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      (∀ n i,
        |Y (min (u n (i + 1)) τ) - Y (min (u n i) τ)| ≤
          |X.drift| * (T / ((n : ℝ) + 2))) ∧
      (∀ δ : ℝ, 0 < δ →
        ∀ᶠ n in atTop, ∀ i,
          |Y (min (u n (i + 1)) τ) - Y (min (u n i) τ)| < δ) := by sorry
