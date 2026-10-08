-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_bounded_variation
-- name    : AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T15:18:03.528358+00:00
-- url     : https://prove2.me/theorems/e068df0b-1a13-4858-a96e-dd12c65f0983
-- title:
--   Finite-horizon verification estimate in the bounded-variation C1 case
-- statement:
--   Bounded-variation core of Proposition 4(i): under the C1 smoothness and HJB hypotheses, every capped admissible strategy has expected discounted dividends up to ruin and deterministic horizon T bounded by w(x). This is the source-faithful finite-horizon change-of-variable estimate before monotone convergence.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, especially the bounded-variation change-of-variable argument leading to the stopped estimate corresponding to (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
