-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
-- name    : AvramDividend.Classical.avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:38:45.992247+00:00
-- url     : https://prove2.me/theorems/5510ba4a-d224-495c-8594-0668ebbe5a6c
-- title:
--   Original finite-horizon no-source-jump prepayment reserve left limit
-- statement:
--   On the original event that the spectrally negative BV source follows its deterministic drift only up to a finite horizon S, and at any positive pre-horizon time, the genuine original controlled-source prepayment left limit has the exact drift-minus-left-dividend formula. This is the local version actually required by the phys95 event, which makes no claim about Lévy jumps after S.
-- source:
--   Original phys95 stopped no-source-jump hypothesis; Proved phys119 and phys123; one-sided eventual equality and Mathlib leftLim_eq_of_tendsto

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys119_original_dividend_rightLimit_eq_strict_rightLim
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys123_original_dividend_leftLim_rightLimit_eq_leftLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys126_original_finite_horizon_zero_source_prepayment_leftLim {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (ω : Ω) (S t : ℝ≥0) (ht : t ≤ S) (hnb : (nhdsWithin t (Iio t)).NeBot) (hsource : ∀ s : ℝ≥0, s ≤ S → X.X s ω = (s : ℝ) * X.drift) : Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = x + (t : ℝ) * X.drift - Function.leftLim (fun s : ℝ≥0 => D s ω) t := by sorry
