-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_postpayment_reserve_rightmesh_converges
-- name    : AvramDividend.Classical.avram_f6_original_true_postpayment_reserve_rightmesh_converges
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:04:55.50172+00:00
-- url     : https://prove2.me/theorems/2a5da977-38b4-4597-a766-a09904b99c29
-- title:
--   Original X minus right-limit D postpayment reserve converges along rightmesh
-- statement:
--   At the true original random subordinate stopping time, the postpayment reserve x+X.X-rightLimit D converges from the right at physical clocks min(tau,sigma+1/(m+1)). Uses only actual original Lévy sample path and dividend right-limit, the previously proved path cadlag/right-continuity, and deterministic physical rightmesh clock convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_rightContinuous
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_continuous_within_clock
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_true_postpayment_reserve_rightmesh_converges
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (k : ℕ) (ω : Ω) :
    Tendsto (fun m : ℕ =>
      x + X.X (min (τ ω) (σ k ω +
        (1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
        rightLimit D (min (τ ω) (σ k ω +
          (1 : ℝ≥0) / ((m : ℝ≥0) + 1))) ω)
      atTop (𝓝 (x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω)) := by sorry
