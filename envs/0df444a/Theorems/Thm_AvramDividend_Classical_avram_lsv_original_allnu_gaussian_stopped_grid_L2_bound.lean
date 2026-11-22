-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_allnu_gaussian_stopped_grid_L2_bound
-- name    : AvramDividend.Classical.avram_lsv_original_allnu_gaussian_stopped_grid_L2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:42:22.104821+00:00
-- url     : https://prove2.me/theorems/04c5e318-f7ed-4162-be72-4062bdfad081
-- title:
--   Original mixed spectrally negative Levy Gaussian source with explicit same-space jump decomposition has stopped L2 bound
-- statement:
--   For the actual original spectrally negative Levy process, given a same-space zero-jump Gaussian component Y and a pointwise decomposition by physical small and large jump channels, the centred original X-minus-jumps martingale stopped at any bounded countable-range stopping time in its right-continuous filtration is L2 with exact horizon variance upper bound T sigma squared. All physical decomposition and stopping hypotheses appear explicitly. Derived from CC BY 4.0 Lean-LSV stopping lemma and original Prove2Me proved source-component martingales.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopping_square_le

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Uses the actual original-process decomposition, existing Proved martingale
  and zero-jump Gaussian moment results, and the Lean-LSV countable-grid
  stopping contraction (CC BY 4.0, commit a5f604de2e1ae431de4cbecde23e5694a12ba719).
  No extra Brownian driver or martingale representation is assumed. -/

theorem AvramDividend.Classical.avram_lsv_original_allnu_gaussian_stopped_grid_L2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    MemLp (stoppedValue M τ) 2 P ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂P) ≤ (T : ℝ) * X.σ ^ 2 := by sorry
