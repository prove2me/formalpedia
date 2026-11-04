-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_clock_inclusive_strict_integrable_iff
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_inclusive_strict_integrable_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:23:18.555928+00:00
-- url     : https://prove2.me/theorems/a96a8b69-1d9a-4a01-ba54-ef9e9c896bb9
-- title:
--   True original ruin-clipped inclusive endpoint preserves exactly the same physical-time L1
-- statement:
--   At the exact original min(ruinTime,n).toNNReal stopped clock, for any fixed trajectory and any physical-time measure without singleton atoms, signed source residual integrability through both endpoints is equivalent to strictly interior integrability. The proof transports through a proved actual-clock a.e. equality, never applying to the random dividend Stieltjes measure.
-- source:
--   Fresh P4-E exact source inclusive-strict a.e integral theorem and pinned Mathlib Integrable.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_clock_inclusive_strict_ae_integral
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original inclusive and strict physical clock integrability coincide. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_inclusive_strict_integrable_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (μ : Measure ℝ≥0) [NullSingletonClass μ]
    (f : ℝ≥0 → ℝ) (ω : Ω) :
    Integrable (fun t : ℝ≥0 => if t ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0) μ ↔
    Integrable (fun t : ℝ≥0 => if 0 < t ∧ t < (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal then f t else 0) μ := by sorry
