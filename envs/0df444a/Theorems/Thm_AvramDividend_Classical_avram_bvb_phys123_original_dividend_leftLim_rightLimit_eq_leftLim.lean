-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
-- name    : AvramDividend.Classical.avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:25:19.34649+00:00
-- url     : https://prove2.me/theorems/004bb92e-a7dd-4d8f-9ddf-ea4d9eb29dad
-- title:
--   Original dividend left limit of rightLimit recovers the dividend left limit
-- statement:
--   At each time with an actual left neighbourhood, the left limit of the original paper's strict-right-limit dividend equals the left limit of the original cumulative dividend path. It uses the proved exact rightLimit identification phys119 and the Mathlib theorem leftLim_rightLim for monotone paths, and is needed to justify the prepayment U in original BV physical-grid quadrature phys95.
-- source:
--   Proved original phys119 rightLimit identity and Mathlib leftLim_rightLim for monotone functions

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (ω : Ω) (t : ℝ≥0) (hnb : (nhdsWithin t (Iio t)).NeBot) : Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) t = Function.leftLim (fun s : ℝ≥0 => D s ω) t := by sorry
