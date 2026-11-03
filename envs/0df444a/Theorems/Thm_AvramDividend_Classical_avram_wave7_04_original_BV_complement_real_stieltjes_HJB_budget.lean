-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_complement_real_stieltjes_HJB_budget
-- name    : AvramDividend.Classical.avram_wave7_04_original_BV_complement_real_stieltjes_HJB_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T12:12:06.15951+00:00
-- url     : https://prove2.me/theorems/3ae3442d-e6cb-4370-aaac-e29ec9813f30
-- title:
--   Original BV strict drift-complement finite-horizon real full Stieltjes HJB expected cash budget
-- statement:
--   For the original stopped bounded-variation spectrally negative Lévy process, every positive-cap admissible dividend strategy has expected real full Stieltjes discounted cash, including the time-zero right-payment atom and pre-ruin continuous dividend mass, bounded above by its HJB supersolution initial value, in the nontrivial strict drift-envelope complement. The expectation is the real expectation of the exact canonical ENNReal fibre cash converted with toReal; no auxiliary sample space or surrogate payout measure is permitted.
-- source:
--   Source-faithful real-expectation sub-obligation of c8770486-df9d-4592-b003-b5072a666878, which itself is the accepted intermediate bridge to canonical ef7e6c20-a118-46f0-ac94-5b02204bba49 in mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Remote-Proved 67f2cfad-5bb0-4c6d-bf93-bdd536e88ad8 converts this exact real budget to the c877 ENNReal conclusion. Genuine work is original-source stopped BV C1 chain, same-filtration predictable negative-jump compensator, zero atom, cap and ruin boundary localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_04_original_BV_complement_real_stieltjes_HJB_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
      w x := by sorry
