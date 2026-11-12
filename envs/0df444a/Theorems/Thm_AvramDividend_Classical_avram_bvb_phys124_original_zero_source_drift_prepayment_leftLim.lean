-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys124_original_zero_source_drift_prepayment_leftLim
-- name    : AvramDividend.Classical.avram_bvb_phys124_original_zero_source_drift_prepayment_leftLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:28:42.162518+00:00
-- url     : https://prove2.me/theorems/93c6ebb5-fcb3-4233-b273-7131fc1e28b9
-- title:
--   Original drift-source BV prepayment reserve has exact left-limit formula
-- statement:
--   On any original admissible controlled BV path, the left limit of its physical no-source-jump drift reserve equals the drift reserve minus the left limit of the cumulative dividend path, at every nonisolated positive time. This reconciles the original prepayment U used inside the stopped marked compensator K in phys95 with the regulated dividend path at a uniform-grid point.
-- source:
--   Proved original phys119 and pending phys123, Mathlib Monotone.tendsto_leftLim and leftLim_eq_of_tendsto

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys124_original_zero_source_drift_prepayment_leftLim {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (ω : Ω) (t : ℝ≥0) (hnb : (nhdsWithin t (Iio t)).NeBot) : Function.leftLim (fun s : ℝ≥0 => x + (s : ℝ) * X.drift - rightLimit D s ω) t = x + (t : ℝ) * X.drift - Function.leftLim (fun s : ℝ≥0 => D s ω) t := by sorry
