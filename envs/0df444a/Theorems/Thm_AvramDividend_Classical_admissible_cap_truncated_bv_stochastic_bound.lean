-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_bound
-- name    : AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T17:45:42.126632+00:00
-- url     : https://prove2.me/theorems/65617e0a-5e27-4272-bb37-8905da7da981
-- title:
--   Stopped change-of-variable verification bound in the bounded-variation case
-- statement:
--   This is the stochastic-calculus boundary of Proposition 4(i) in the bounded-variation case. Assume directly the analytic consequences used by the verification argument: generator integrability and Γw-qw≤0, the marginal-dividend inequality w'≥1, non-negativity of the stopped terminal verification value before ruin, C1 regularity, and w=0 below zero. Then the expected discounted dividends up to ruin and a deterministic horizon are bounded by w(x). The intended proof is the finite-variation change-of-variable formula applied to the controlled reserve, with the continuous dividend term controlled by w'≥1, lump-sum terms controlled by the derivative inequality/admissibility, the generator drift nonpositive, and localisation/expectation.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, bounded-variation branch of the proof leading to the stopped estimate (5.13). This child deliberately starts after all elementary HJB consequences have been extracted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
