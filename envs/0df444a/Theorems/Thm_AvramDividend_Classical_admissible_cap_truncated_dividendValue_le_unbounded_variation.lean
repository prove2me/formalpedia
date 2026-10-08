-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_unbounded_variation
-- name    : AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T15:18:33.161426+00:00
-- url     : https://prove2.me/theorems/cc518136-9d63-4167-8587-606274d8eec9
-- title:
--   Finite-horizon verification estimate in the unbounded-variation C2 case
-- statement:
--   Unbounded-variation core of Proposition 4(i): under the C2 smoothness and HJB hypotheses, every capped admissible strategy has expected discounted dividends up to ruin and deterministic horizon T bounded by w(x). This isolates the source-faithful stopped Itô/localisation estimate before monotone convergence.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, the C2 Itô/localisation argument leading to the stopped estimate corresponding to (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
