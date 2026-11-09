-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
-- name    : AvramDividend.Classical.avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:02:03.998203+00:00
-- url     : https://prove2.me/theorems/dc73fa6f-3bbe-41e6-a486-9548ce8858df
-- title:
--   Original BV arbitrary-adapted postpayment zero-contact restart Stieltjes cash identity
-- statement:
--   In the physical original BV spectrally negative process with finite negative-jump activity, for arbitrary adapted admissible dividend D, an interval whose postpayment reserves are zero at both endpoints has actual Stieltjes cash on the half-open interval equal to the physical source increment. If the source has its drift increment, the mass is exactly drift times duration. The starting right-payment atom is excluded and the ending right-payment atom is included by the Ioc chronology; this permits restart immediately after a dividend lump that reduces reserve to zero. No auxiliary compound-Poisson process, stopping-time measurability or conditional jump independence is assumed.
-- source:
--   Direct original process algebra using IsAdmissibleLe underlying IsDividendStrategy, riskProcess definition and Proved dividendMeasure_Ioc_rightLimit f9211de0; complementary to Proved 28a916cf which only covers prepayment-zero endpoints.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_postpayment_zero_Ioc_cash_eq_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hpostzeroa : riskProcess X x D a ω -
      (rightLimit D a ω - D a ω) = 0)
    (hpostzerob : riskProcess X x D b ω -
      (rightLimit D b ω - D b ω) = 0)
    (hline : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ))) := by sorry
