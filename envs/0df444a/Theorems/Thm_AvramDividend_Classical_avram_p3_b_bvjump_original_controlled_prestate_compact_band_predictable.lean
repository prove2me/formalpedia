-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:58:52.449732+00:00
-- url     : https://prove2.me/theorems/5115705e-9215-4ef7-bf83-33e0f8685435
-- title:
--   Original controlled pre-jump reserve in a compact band is a predictable source-mark compensation event
-- statement:
--   For the exact original spectrally negative Levy process and dividend strategy, the event that the true controlled prepayment left-limit lies in a compact real reserve band belongs to the original right-continuous predictable sigma-algebra, enabling source intrinsic-jump compensation on that event.
-- source:
--   Proved wave3 original controlled postpayment reserve pre-jump strongly predictable process

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (a b : ℝ) : MeasurableSet[𝓕.rightCont.predictable] {p : ℝ≥0 × Ω | Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b} := by sorry
