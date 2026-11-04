-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_right_atom_cash_to_real
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_right_atom_cash_to_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:50:45.9242+00:00
-- url     : https://prove2.me/theorems/2a049ee7-1a0f-4c45-b655-009bd54fd91c
-- title:
--   Original right-dividend singleton discounted cash exactly equals the physical right jump at a valid stopped payment
-- statement:
--   Use the original right-continuous dividend Stieltjes singleton identity on the complete closed [0,T] window to convert ENNReal discounted atom mass to the actual right-limit increment, with the exact original paymentTimes(ruinTime) selector and proper source-first/right-dividend-second ordering. The nonnegative right increment is stated explicitly as a checkable property of increasing admissible controls. Time zero and the surviving horizon remain eligible; positive ruin atoms remain excluded by paymentTimes.
-- source:
--   Original paper Proposition 4(i), Eq. 5.13; source-proved d19177af full closed Stieltjes atomic/diffuse and endpoint singleton identity; Mathlib ENNReal.ofReal_mul and ENNReal.toReal_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_right_atom_cash_to_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T t : ℝ≥0) (ht : t ≤ T)
    (hδ : 0 ≤ rightLimit D t ω - D t ω) (q : ℝ) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    (μ {(t : ℝ)} *
      (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
        else 0)).toReal =
      if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then (rightLimit D t ω - D t ω) * Real.exp (-(q * (t : ℝ)))
        else 0 := by sorry
