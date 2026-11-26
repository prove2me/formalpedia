-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_grid_band_nested_cover
-- name    : AvramDividend.Classical.avram_locmoll_grid_band_nested_cover
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T22:04:34.530658+00:00
-- url     : https://prove2.me/theorems/d91b812f-306a-5d1a-b89a-dba59215abb6
-- title:
--   Nested capped grid clocks are monotone and cover every compact in-band prefix
-- statement:
--   Nested capped grid clocks are monotone and cover every compact in-band prefix
-- source:
--   Exact grid clock decomposition of 4ea65782-b369-53ec-b8f2-333535678261

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_grid_band_nested_cover
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
    (∀ ω, Monotone (fun k => θ k ω)) ∧
    (∀ k ω t, t ≤ H → (∀ s : ℝ≥0, s ≤ t → Y s ω ∈ Icc (δ k) (R k)) →
      t ≤ θ k ω) := by sorry
