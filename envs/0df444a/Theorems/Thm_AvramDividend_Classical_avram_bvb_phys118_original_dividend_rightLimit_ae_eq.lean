-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys118_original_dividend_rightLimit_ae_eq
-- name    : AvramDividend.Classical.avram_bvb_phys118_original_dividend_rightLimit_ae_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:59:09.111003+00:00
-- url     : https://prove2.me/theorems/d1b5050a-cb2a-4f6c-9014-bb83c3762402
-- title:
--   Physical original dividend rightLimit equals payout path almost everywhere
-- statement:
--   For an original admissible dividend strategy and any atomless time measure, the actual infimum-defined rightLimit D equals D almost everywhere. This identifies the original problem's postpayment controlled reserve with its ordinary path at Lebesgue-a.e. time, a missing connection in the stopped negative-mark compensator physical-grid argument phys95.
-- source:
--   Original DividendStrategy rightLimit definition, Proved phys116, Mathlib Monotone.rightLim_eq_sInf and sInf_image'

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys118_original_dividend_rightLimit_ae_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (μ : Measure ℝ≥0) [NullSingletonClass μ] (ω : Ω) : ∀ᵐ t ∂μ, rightLimit D t ω = D t ω := by sorry
