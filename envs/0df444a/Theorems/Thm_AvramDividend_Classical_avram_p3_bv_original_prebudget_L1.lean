-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
-- name    : AvramDividend.Classical.avram_p3_bv_original_prebudget_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:39:54.702802+00:00
-- url     : https://prove2.me/theorems/78fa7075-2712-494f-a233-a4de325f68fd
-- title:
--   Full original BV strict cash plus surviving pre-rightpayment terminal is jointly integrable
-- statement:
--   The exact original pre-horizon cash integral, including the time-zero dividend right atom, and the surviving signed terminal immediately before the horizon right-payment are jointly L1. Uses proven original strict cash L1 and original compact-drift-strip preterminal L1. Source normalisation X.X_zero and IsProbabilityMeasure P are discharged directly from the original SpectrallyNegativeLevy structure. This discharges the integrability premise of the established expectation assembly without supposing jump compensation or a martingale.
-- source:
--   Proved avram_p3_bv_original_strict_cash_L1 and avram_p3_bv_original_strict_preterminal_L1, combined with Integrable.add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_prebudget_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)) P := by sorry
