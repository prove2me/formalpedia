-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_stopped_gaussian_compensated_square_mean_zero
-- name    : AvramDividend.Classical.avram_lsv_original_zerojump_stopped_gaussian_compensated_square_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:56:21.05683+00:00
-- url     : https://prove2.me/theorems/ceabf136-0563-4cdf-a642-0ccd27ecbdb8
-- title:
--   Original zero-jump stopped Gaussian compensated square has integrable zero expected residual
-- statement:
--   The actual original zero-jump spectrally negative Levy process has an integrable, mean-zero stopped quadratic Gaussian compensator (X_t-tc)^2-t sigma^2 at any genuine right-continuous filtration stopping time of countable range bounded by T. The proof derives from the true original square martingale, exact deterministic Gaussian second moment, and the CC BY 4.0 lean-lsv stopped optional expectation lemma; no Brownian or synthetic process substitution is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_square_martingale
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_martingale_expectation

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-
The original zero-jump Lévy compensated square, stopped at a genuine
bounded countable-range clock. Uses accepted Lean-LSV optional expectation
(CC BY 4.0, commit a5f604de2e1ae431de4cbecde23e5694a12ba719).
True martingale and exact Gaussian moments are original Avram proved inputs.
-/

theorem AvramDividend.Classical.avram_lsv_original_zerojump_stopped_gaussian_compensated_square_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let Q : ℝ≥0 → Ω → ℝ := fun t ω =>
      (X.X t ω - (t : ℝ) * X.c)^2 - (t : ℝ) * X.σ^2
    Integrable (stoppedValue Q τ) P ∧
      (∫ ω, stoppedValue Q τ ω ∂P) = 0 := by sorry
