-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b69_original_true_spatial_clock_ruin_clipped
-- name    : AvramDividend.Classical.avram_b69_original_true_spatial_clock_ruin_clipped
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:40:10.375181+00:00
-- url     : https://prove2.me/theorems/018573a2-595e-4579-b715-7fad23e0884b
-- title:
--   Original true spatial-stopped physical clock stays below the ruin and horizon clocks
-- statement:
--   The exact source upper-exit localising clock kappa(k) constructed as min(rho, original upper-exit) never exceeds rho or the original ruinTime when rho is ruin/horizon clipped. Includes the zero-clock case; never invokes any post-ruin path extension or approximating clock.
-- source:
--   Original definitions of ruinTime and twoSidedExitUpTime and p4 finite-mixed ruin-clipped exact clock; ENNReal.toNNReal_mono and ENNReal.coe_toNNReal at pinned Mathlib revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b69_original_true_spatial_clock_ruin_clipped
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) :
    ∀ k ω, κ k ω ≤ ρ ω ∧
      (κ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by sorry
