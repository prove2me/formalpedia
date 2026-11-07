-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_mass_positive_DCT_for_random_errors
-- name    : AvramDividend.Classical.avram_bv_error7_original_BV_mass_positive_DCT_for_random_errors
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:18:24.423001+00:00
-- url     : https://prove2.me/theorems/9a6f4aa1-c970-4b01-9a30-14766075616c
-- title:
--   Original bounded-variation source first moment gives positive-part DCT for sample-dependent measurable errors
-- statement:
--   On the original bounded-variation spectrally negative Levy probability space, the genuine finite-horizon source mass |X.drift| T + |T X.drift - X_T| is L1 for T≤1. Therefore any strongly a.e.-measurable real error sequence, including errors formed using sample-dependent stopped physical grids, that is bounded by a fixed multiple of this exact source mass and tends to zero almost surely has integrable positive parts and expected positive parts tending to zero. This is the precise positive-error absorption step needed for random-grid Fatou, with honest domination and no inference solely from pointwise convergence. It does not use the BV prebudget or signed source.
-- source:
--   Source-exact extraction of the already accepted genuine original dominated convergence argument 70a2660b-af9a-4e0c-9e31-a0cf5eed04e9; uses the separately Proved original BV first-moment theorem 09287ead-652a-4521-8a54-ac198d1c917b. The original stochastic process is fixed and unaltered.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_BV_mass_positive_DCT_for_random_errors
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (Err : ℕ → Ω → ℝ)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      ‖Err m ω‖ ≤ K * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|)) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
