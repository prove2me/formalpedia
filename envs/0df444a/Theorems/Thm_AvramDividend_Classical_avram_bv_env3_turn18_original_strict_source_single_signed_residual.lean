-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn18_original_strict_source_single_signed_residual
-- name    : AvramDividend.Classical.avram_bv_env3_turn18_original_strict_source_single_signed_residual
-- status  : Open
-- author  : @WillR
-- created : 2026-11-05T23:41:27.145194+00:00
-- url     : https://prove2.me/theorems/da179c64-3a1c-41fd-85dd-2c3029bd23bf
-- title:
--   Original BV stopped strict cash has one integrable signed residual of nonpositive expectation
-- statement:
--   For the original bounded-variation spectrally negative Lévy process and admissible dividend strategy satisfying the positive-interior HJB and dividend-jump sign premises, the stopped strict dividend cash plus surviving pre-rightpayment terminal is bounded almost everywhere by w(x)+R for one integrable residual R of nonpositive expectation. This deliberately combines compensated jump martingale and signed HJB drift into one quantity, avoiding a synthetic law change, and preserves strict ruin and horizon atom conventions.
-- source:
--   Genuine original stopped C1 finite-variation Ito plus predictable compensated negative-jump source from Avram, Palmowski and Pistorius verification, with existing accepted sources 3e11dc25, 3bf70c3c, 1359bfd0, 04dadbf6, 3497711e. This is the exact source-hard child for c877 via proven 29940c1c single-signed-witness-to-closed-cash bridge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn18_original_strict_source_single_signed_residual
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
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ R : Ω → ℝ, Integrable R P ∧
      (∫ ω, R ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D ⟨T, hT⟩ ω)
         else 0) ≤ w x + R ω) := by sorry
