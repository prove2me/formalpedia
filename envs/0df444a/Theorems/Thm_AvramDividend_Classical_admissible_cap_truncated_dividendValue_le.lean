-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le
-- name    : AvramDividend.Classical.admissible_cap_truncated_dividendValue_le
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T10:01:45.320571+00:00
-- url     : https://prove2.me/theorems/6c39765b-1cba-4af6-8406-6ab4db002ef4
-- title:
--   Finite-horizon verification inequality for one capped dividend strategy
-- statement:
--   Under the hypotheses of Proposition 4(i), the expected discounted dividends of any capped admissible policy, restricted to payments no later than a deterministic finite horizon T and before ruin, are at most w(x). This is the finite-horizon/localised verification estimate obtained from Ito's formula in the unbounded-variation case or the C1 change-of-variable formula in the bounded-variation case, including continuous and lump-sum dividends.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 4(i), proof around equation (5.13), pp. 18-19. Finite-horizon form isolating the stochastic calculus step before monotone convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_dividendValue_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
