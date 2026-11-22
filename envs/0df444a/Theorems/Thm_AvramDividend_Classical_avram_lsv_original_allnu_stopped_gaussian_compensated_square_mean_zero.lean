-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_allnu_stopped_gaussian_compensated_square_mean_zero
-- name    : AvramDividend.Classical.avram_lsv_original_allnu_stopped_gaussian_compensated_square_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:57:29.279946+00:00
-- url     : https://prove2.me/theorems/78a55477-29da-4464-a2bc-538072c5304a
-- title:
--   Original mixed Levy stopped physical Gaussian quadratic compensator is integrable and mean zero
-- statement:
--   For an original spectrally negative Levy process X with genuine same-space zero-jump Gaussian process Y and explicitly given physical small and large jump channels whose pathwise decomposition reconstructs X, its square-compensated original continuous source (X-tc-Jsmall-Jlarge)^2-t sigma^2 is integrable and has mean zero after any bounded countable-range stopping time of the original right-continuous filtration. Uses proved physical martingale and LSV optional expectation, not a hypothetical driver. Source Lean-LSV CC BY 4.0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_martingale_expectation

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Actual original X-minus-physical-jumps stopped Gaussian compensated square.
   Uses proved same-space Gaussian decomposition, square martingale and the
   Lean-LSV bounded countable-range optional expectation (CC BY 4.0,
   original upstream commit a5f604de2e1ae431de4cbecde23e5694a12ba719). -/

theorem AvramDividend.Classical.avram_lsv_original_allnu_stopped_gaussian_compensated_square_mean_zero
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
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (M t ω)^2 - (t : ℝ) * X.σ^2
    Integrable (stoppedValue Q τ) P ∧
      (∫ ω, stoppedValue Q τ ω ∂P) = 0 := by sorry
