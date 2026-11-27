-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_grid_band_bound_prefix
-- name    : AvramDividend.Classical.avram_locmoll_grid_band_bound_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:04:21.19188+00:00
-- url     : https://prove2.me/theorems/c82d22cc-0163-4842-951d-d454bed363ed
-- title:
--   Capped dense grid clocks have bounded horizon and physical prefix band
-- statement:
--   Capped dense grid clocks have bounded horizon and physical prefix band
-- source:
--   Exact grid clock decomposition of 4ea65782-b369-53ec-b8f2-333535678261

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_grid_band_bound_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (H : ℝ≥0) (δ R : ℕ → ℝ)
    (hδ : Antitone δ) (hR : Monotone R)
    (r : ℕ → ℝ≥0) (hr : DenseRange r) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
    let E : ℕ → Ω → ℕ → ℝ≥0 := fun k ω j =>
      if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H
    let θ : ℕ → Ω → ℝ≥0 := fun k ω => ⨅ j, E k ω j
    (∀ k ω, θ k ω ≤ H) ∧
    (∀ k ω t, t < θ k ω → Y t ω ∈ Icc (δ k) (R k)) := by sorry
