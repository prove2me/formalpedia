-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_gaussian_stopped_grid_L2_bound
-- name    : AvramDividend.Classical.avram_lsv_original_zerojump_gaussian_stopped_grid_L2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:40:53.543185+00:00
-- url     : https://prove2.me/theorems/eedcc495-680a-467e-9bcc-a4ec302a7716
-- title:
--   Original zero-jump spectrally negative Levy Gaussian martingale stopped L2 bracket bounded by sigma squared times horizon
-- statement:
--   For the original spectrally negative Levy process with zero Levy measure, its actual centred Gaussian path X_t-tc is a true martingale; at a bounded countable-range stopping time in the right-continuous original filtration its stopped value is L2 and its expected square is at most T sigma squared. This instantiates the genuine accepted LSV stopping contraction using the existing original-process martingale and exact deterministic second-moment theorems, retaining every stopping and measurability hypothesis. Derived from the lean-lsv stopping result, CC BY 4.0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopping_square_le

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- This is the original-process instantiation of the countable-grid stopping
   contraction adapted from dufeteller/lean-lsv, LSV/LocalizedStoppingL2Convergence,
   commit a5f604de2e1ae431de4cbecde23e5694a12ba719, CC BY 4.0.
   Original-process martingale and moment inputs are already Proved in Prove2Me. -/

theorem AvramDividend.Classical.avram_lsv_original_zerojump_gaussian_stopped_grid_L2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let M : ℝ≥0 → Ω → ℝ := fun s ω => X.X s ω - (s : ℝ) * X.c
    MemLp (stoppedValue M τ) 2 P ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂P) ≤ (T : ℝ) * X.σ ^ 2 := by sorry
