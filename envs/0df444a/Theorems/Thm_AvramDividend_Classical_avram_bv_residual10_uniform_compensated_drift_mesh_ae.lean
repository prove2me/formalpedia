-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_uniform_compensated_drift_mesh_ae
-- name    : AvramDividend.Classical.avram_bv_residual10_uniform_compensated_drift_mesh_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:20:19.441914+00:00
-- url     : https://prove2.me/theorems/76e0d4ac-ffb0-49e7-b3b9-118390010517
-- title:
--   Original bounded-variation Levy jump-compensated uniform-grid drift increments vanish almost surely
-- statement:
--   For every Standing bounded-variation spectrally negative Levy process, on one common full-probability event the original process plus its exact negative-jump path correction has deterministic drift increments on every index of the canonical refining physical uniform grid. The cell increments equal drift times cell width and vanish uniformly over all grid indices. This removes the conditional pathwise representation premise from the previously Proved mesh theorem, without introducing Brownian substitution, stopping-time modifications or alternate dividends. The subsequent stopped cash and positive-part Taylor error estimates remain independent obligations.
-- source:
--   AVRAM BV-RESIDUAL10 round 8, original BV process plus two Proved source interfaces, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_uniform_compensated_drift_mesh_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P,
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
