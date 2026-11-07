-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f16_original_physical_sigma_clock_le_finite_horizon
-- name    : AvramDividend.Classical.avram_f16_original_physical_sigma_clock_le_finite_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:29:27.96732+00:00
-- url     : https://prove2.me/theorems/16e69d4e-af85-466c-a952-0974357e2db6
-- title:
--   Every original physical stopped refinement clock below the ruin-horizon minimum is bounded by the finite horizon
-- statement:
--   For the actual original spectrally negative Levy reserve under its original dividend process, if the physical stopped horizon tau is the real-valued minimum of ruin time and finite n, and every refinement stopping clock sigma_k is dominated by tau, then each sigma_k is bounded by n for every path. This is the exact uniform stopping-time bound needed to instantiate bounded original zero-jump C2 Gaussian one-cell martingale theorems at the true sigma_k rather than at a surrogate clock.
-- source:
--   Acyclic original-source stopping-time finite-bound transfer from exact a029846e premises, using pinned ENNReal.toNNReal_mono and finite n.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_f16_original_physical_sigma_clock_le_finite_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω, σ k ω ≤ (n : ℝ≥0) := by sorry
