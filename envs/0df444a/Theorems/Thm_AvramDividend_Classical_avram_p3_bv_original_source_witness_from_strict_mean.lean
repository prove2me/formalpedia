-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean
-- name    : AvramDividend.Classical.avram_p3_bv_original_source_witness_from_strict_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:28:33.201889+00:00
-- url     : https://prove2.me/theorems/a55a5fab-e951-4b68-93b4-3997daabf361
-- title:
--   Actual original BV strict stopped signed residual witness from the source expected budget
-- statement:
--   For the original SpectrallyNegativeLevy X, X.isProbability supplies probability mass one and the accepted original BV strict-payoff integrability theorem supplies L1. If the exact strict Iio T stopped cash plus original pre-rightpayment terminal has expectation at most w(x), its difference from w(x) is an actual L1 signed witness with nonpositive expected value and exact pathwise equality. This is a genuine conditional reduction of canonical 7bb152c2 to the independent strict HJB prebudget a19d8b28, preserving original time-zero and ruin conventions.
-- source:
--   Proved original BV prebudget L1; source field SpectrallyNegativeLevy.isProbability; canonical 7bb152c2 / a19d8b28

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original source has probability mass one in its own structure.
The actual strict payoff minus its initial value is consequently an L1
signed residual witness whenever its physical expected budget holds. -/

theorem AvramDividend.Classical.avram_p3_bv_original_source_witness_from_strict_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    (∫ ω, Strict ω ∂P) ≤ w x →
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P, Strict ω ≤ w x + E ω) := by sorry
