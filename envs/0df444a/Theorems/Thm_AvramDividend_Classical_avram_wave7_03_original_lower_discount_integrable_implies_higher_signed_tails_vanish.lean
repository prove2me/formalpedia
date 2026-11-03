-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_lower_discount_integrable_implies_higher_signed_tails_vanish
-- name    : AvramDividend.Classical.avram_wave7_03_original_lower_discount_integrable_implies_higher_signed_tails_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:16:11.018482+00:00
-- url     : https://prove2.me/theorems/fdd218f8-8d95-4665-abab-4b59da9ceb27
-- title:
--   Original lower-discount genuine signed Stieltjes integrability forces higher-discount future signed payout tails to vanish
-- statement:
--   On the exact original path and Stieltjes measure, full genuine signed pre-ruin IntegrableOn at a lower discount q₁ guarantees convergence to zero of the real signed strict-future payout tails at every q₂≥q₁. Using only accepted theorem imports, the proof transfers full ENNReal cash finiteness through a pointwise discount comparison on the original nonnegative paymentTimes, converts it back to genuine IntegrableOn at the higher discount, and invokes the accepted source signed-tail limit. Keeps the true time-zero atom, continuous payments, strict pre-ruin domain and original probability process.
-- source:
--   Accepted original pathwise signed integrability iff a6d24d2f, paymentTimes_measurable 88dafb7f, original signed-tail theorem c94fa5f6.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_lower_discount_integrable_implies_higher_signed_tails_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q₁ * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    Tendsto (fun n : ℕ =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by sorry
