-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_subordinate_clock_le_ruin
-- name    : AvramDividend.Classical.avram_jump6_B_original_subordinate_clock_le_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T16:27:51.573778+00:00
-- url     : https://prove2.me/theorems/a5216ca1-3a72-41b6-88b9-3520e20d304e
-- title:
--   Each original subordinate stopped clock lies before the original ruin time
-- statement:
--   For original spectrally negative Levy X and dividend process D, if tau is the genuine capped ruin time min(ruinTime X x D, N), and each subordinate sigma(k) lies before tau, then sigma(k) is no later than the original ruin time. The proof uses the Mathlib ENNReal coercion inequality for the finite ruin-truncated clock. No independence, finite intensity or stochastic representation is assumed. This directly supplies the clock-before-ruin premise in the genuine source physical-grid certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_subordinate_clock_le_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (N : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (N : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by sorry
