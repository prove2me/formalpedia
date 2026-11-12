-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys122_original_zero_source_postpayment_eq_risk_ae
-- name    : AvramDividend.Classical.avram_bvb_phys122_original_zero_source_postpayment_eq_risk_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:31:02.467207+00:00
-- url     : https://prove2.me/theorems/2a56ab15-966b-44c7-9751-6e062f6d8f64
-- title:
--   Original zero-source-jump postpayment reserve equals risk almost everywhere
-- statement:
--   On any original sample path with no Lévy source jumps and linear BV drift, the exact postpayment reserve x+drift·t−rightLimit D(t) equals the ordinary prepayment controlled risk process almost everywhere for any atomless time measure. This is the continuous-time identification needed in the actual phys95 one-sided compensated mark quadrature, without any auxiliary probability space.
-- source:
--   Original no-source-jump path hypothesis and Proved phys118 a.e. original dividend rightLimit equality

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys118_original_dividend_rightLimit_ae_eq
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys122_original_zero_source_postpayment_eq_risk_ae {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (μ : Measure ℝ≥0) [NullSingletonClass μ] (ω : Ω) (hpath : ∀ t : ℝ≥0, X.X t ω = (t : ℝ) * X.drift) : ∀ᵐ t ∂μ, x + ((t : ℝ≥0) : ℝ) * X.drift - rightLimit D t ω = riskProcess X x D t ω := by sorry
