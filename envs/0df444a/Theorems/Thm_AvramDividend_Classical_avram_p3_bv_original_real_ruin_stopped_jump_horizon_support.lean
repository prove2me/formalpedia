-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_ruin_stopped_jump_horizon_support
-- name    : AvramDividend.Classical.avram_p3_bv_original_real_ruin_stopped_jump_horizon_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:50:39.036147+00:00
-- url     : https://prove2.me/theorems/78546651-0992-4ec9-aa89-ca757414b532
-- title:
--   Original real-horizon ruin-stopped intrinsic jump integrand has exact physical horizon support
-- statement:
--   The genuine finite real-horizon ruin stopping clock of the original dividend-controlled spectrally negative Lévy process is never beyond original ruin. Every integrand multiplied by its exact stopping indicator is unchanged by the physical set indicator {time ≤ T}. This discharges the hτruin and hSupport hypotheses in existing original stopped negative-jump and BV verification results without an auxiliary clock.
-- source:
--   Accepted source-exact arbitrary real-horizon original ruin-clock bound 712c7638, finite ENNReal cast identity and physical stopping indicator definition. No stochastic approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_truncated_ruin_nnreal_stopping

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_real_ruin_stopped_jump_horizon_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let S : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.1.1 ≤ T}
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    (∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) ∧
      S.indicator H = H := by sorry
