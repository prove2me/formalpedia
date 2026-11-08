-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_uniform_compensated_drift_mesh
-- name    : AvramDividend.Classical.avram_bv_residual10_original_uniform_compensated_drift_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:38:37.070011+00:00
-- url     : https://prove2.me/theorems/1cfb9c7c-327a-4242-80e7-2348cf5ffa7f
-- title:
--   Exact original BV jump-compensated drift increments vanish on the refining uniform physical mesh
-- statement:
--   Under the exact original pathwise Lévy drift-minus-negative-jump representation, the intrinsic compensated path X plus its jump correction is precisely linear in physical time. At every point of the canonical refining uniform grid, each compensated increment is the deterministic drift times the uniform cell width, and the maximum absolute increment tends to zero. The theorem proves the source-exact mesh increment interface required by compact-band original C1 Taylor error estimates but leaves jump-path representation, stopping, band inclusion, and dividend atom accounting as explicit separate obligations.
-- source:
--   AVRAM BV-RESIDUAL10, original uniform-grid intrinsic path jump correction, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_uniform_compensated_drift_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hpath : ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) =
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    (∀ n i, Y (u n (i + 1)) - Y (u n i) =
      X.drift * (T / ((n : ℝ) + 2))) ∧
    (∀ δ : ℝ, 0 < δ →
      ∀ᶠ n in atTop, ∀ i,
        |Y (u n (i + 1)) - Y (u n i)| < δ) := by sorry
