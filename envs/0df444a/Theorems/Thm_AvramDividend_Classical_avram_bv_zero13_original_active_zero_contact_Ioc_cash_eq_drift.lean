-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
-- name    : AvramDividend.Classical.avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:32:44.6552+00:00
-- url     : https://prove2.me/theorems/28a916cf-7c9b-4eb7-82ba-f83b28e0fdcc
-- title:
--   Original BV finite-activity zero-contact Stieltjes cash equals physical drift over a source-linear interval
-- statement:
--   For the genuine original bounded-variation spectrally negative Levy process with finite negative-jump intensity and arbitrary admissible adapted left-continuous dividends D, if both ends of an active interval have pre-rightpayment reserve exactly zero and the original physical source X grows by drift times duration, the actual half-open Stieltjes dividend cash on that interval equals that drift increment. This remains valid for pathwise chosen restart endpoints, excludes the first endpoint right-payment atom, includes the final endpoint only if admissibly active, and uses no auxiliary compound-Poisson process. Establishing the physical source-linear no-negative-jump interval and random-endpoint measurability is left to the parent stopped-source proof.
-- source:
--   Exact source identity from riskProcess X x D = x + X.X - D, IsAdmissibleLe right-payment constraint at active zero reserve, dividendStrategy_le_rightLimit and dividendMeasure_Ioc_rightLimit. Consumer 73419313 / 6211514c original finite/top cap stopped HJB source; no stochastic first-jump law is postulated.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_active_zero_contact_Ioc_cash_eq_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hactivea : a = 0 ∨ (a : ℝ≥0∞) < ruinTime X x D ω)
    (hactiveb : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω)
    (hzeroa : riskProcess X x D a ω = 0)
    (hzerob : riskProcess X x D b ω = 0)
    (hline : X.X b ω - X.X a ω =
      X.drift * ((b : ℝ) - (a : ℝ))) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (X.drift * ((b : ℝ) - (a : ℝ))) := by sorry
