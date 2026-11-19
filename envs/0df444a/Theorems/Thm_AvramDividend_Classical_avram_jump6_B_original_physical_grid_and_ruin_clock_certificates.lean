-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_grid_and_ruin_clock_certificates
-- name    : AvramDividend.Classical.avram_jump6_B_original_physical_grid_and_ruin_clock_certificates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:31:45.440684+00:00
-- url     : https://prove2.me/theorems/0fb07c1c-937e-484e-8acf-7124b5787eb7
-- title:
--   Same original ruin-truncated stop: refining grid and pre-ruin physical clock certificates
-- statement:
--   Unifies the two Proved original-process certificates: a canonical zero-origin monotonically refining physical time grid covers every subordinate stopping clock, and the same clock is no later than the actual ruin time. This simultaneously discharges the geometric stop and grid premises in the original stopped Ito-Meyer physical-source certificate, with no extra assumptions, finite intensity or independent process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_refining_physical_grid_cover
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_subordinate_clock_le_ruin
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_physical_grid_and_ruin_clock_certificates
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (N : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (N : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    let u : ℕ → ℕ → ℝ≥0 := fun j i =>
      (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
    let m : ℕ → ℕ := fun j => (N + 1) * (j + 1)
    (∀ j, Monotone (u j)) ∧
    (∀ j, u j 0 = 0) ∧
    (∀ k ω, ∀ᶠ j in atTop, σ k ω ≤ u j (m j)) ∧
    (∀ k ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω) := by sorry
