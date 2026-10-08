-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_ubv_stochastic_bound
-- name    : AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T17:45:29.648303+00:00
-- url     : https://prove2.me/theorems/f5cc2d5c-9551-4859-adbb-b39fe0cc7414
-- title:
--   Stopped Itô verification bound in the unbounded-variation case
-- statement:
--   This is the stochastic-calculus boundary of Proposition 4(i) in the unbounded-variation case. Assume directly generator integrability and Γw-qw≤0, w'≥1, non-negativity of the terminal verification value before ruin, C2 regularity, and w=0 below zero. Then the expected discounted dividends up to ruin and deterministic horizon T are bounded by w(x). The intended proof is the stopped/localised Itô formula for e^{-qt}w(U_t), with Lévy generator drift, martingale expectation zero, continuous and lump-sum dividend terms, and the nonnegative terminal term.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4, unbounded-variation C2 Itô/localisation branch leading to the stopped estimate (5.13). This child begins after the deterministic HJB inequalities have already been proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
