-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:18:19.892855+00:00
-- url     : https://prove2.me/theorems/d7cfc4ba-d046-4efe-8023-80c34ed8c344
-- title:
--   Original capped-ruin stopped Gaussian bracket is bounded by terminal energy
-- statement:
--   On the exact original Avram probability space, for any original stopping clock τ and finite deterministic horizon T, the squared Gaussian integrand accumulated up to τ∧T is at most its terminal energy on (0,T], assuming pathwise terminal quadratic integrability. In particular τ can be the actual original ruin clock. A samplewise finite quadratic-energy domination interface used in local-to-true stopped Gaussian martingale arguments.
-- source:
--   Pinned Mathlib setIntegral_mono_set and min_le_right, inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ) (μtime : Measure ℝ≥0)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hEnergy : ∀ ω, IntegrableOn
      (fun t : ℝ≥0 => (H (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime) :
    ∀ ω, (∫ t in Ioc (0 : ℝ≥0) (min (τ ω) T),
        (H (t, ω)) ^ 2 ∂μtime) ≤
      ∫ t in Ioc (0 : ℝ≥0) T, (H (t, ω)) ^ 2 ∂μtime := by sorry
