-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_grid_band_clock_family
-- name    : AvramDividend.Classical.avram_locmoll_grid_band_clock_family
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T22:02:05.417909+00:00
-- url     : https://prove2.me/theorems/4ea65782-b369-53ec-b8f2-333535678261
-- title:
--   Capped strict exterior grid clocks: stopping, nestedness, prefix band, and compact coverage
-- statement:
--   Capped strict exterior grid clocks: stopping, nestedness, prefix band, and compact coverage
-- source:
--   Exact decomposition of 1956f1aa-dda2-5052-8723-910f7fb63181, Avram Proposition 4(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_grid_band_clock_family
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (H : ℝ≥0) (δ R : ℕ → ℝ)
    (hδ : Antitone δ) (hR : Monotone R) :
    ∃ θ : ℕ → Ω → ℝ≥0,
      (∀ k ω, θ k ω ≤ H) ∧
      (∀ k ω t, t < θ k ω → x + X.X t ω - rightLimit D t ω ∈ Icc (δ k) (R k)) ∧
      (∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (θ k ω : WithTop ℝ≥0))) ∧
      (∀ ω, Monotone (fun k => θ k ω)) ∧
      (∀ k ω t, t ≤ H →
        (∀ s : ℝ≥0, s ≤ t → x + X.X s ω - rightLimit D s ω ∈ Icc (δ k) (R k)) →
        t ≤ θ k ω) := by sorry
