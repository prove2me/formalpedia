-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8c_original_B_deep_negative_tail_integrable
-- name    : AvramDividend.Classical.avram_p3_grid4_turn8c_original_B_deep_negative_tail_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:19:31.393778+00:00
-- url     : https://prove2.me/theorems/d26dbb61-388d-4913-b4c4-3e46756ae919
-- title:
--   Authentic BV signed source has an integrable negative tail beyond its constant cash reserve
-- statement:
--   Without any finite-total-mass assumption, the exact original strict cash budget and positivity force the excess negative signed HJB source beyond the deterministic initial reserve max(w x,0) to be L1. The remaining bounded constant reserve portion requires finite measure to infer global B integrability; this is a genuine source-faithful localisation bridge, conditional on the actual pathwise stopped-grid inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_turn8c_original_B_deep_negative_tail_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (S : ℝ≥0)
    (hS : S = ⟨T, hT⟩) (δ : ℕ → ℝ)
    (Pay M B Err : ℕ → Ω → ℝ)
    (hPayExact : ∀ n ω, Pay n ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
         Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0))
    (hM : ∀ n, Integrable (M n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (B n) P)
    (hBNeg : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPayPos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Pay n ω)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      Pay n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0) :
    ∀ n, Integrable (fun ω => max (-(B n ω) - max (w x) 0) 0) P := by sorry
