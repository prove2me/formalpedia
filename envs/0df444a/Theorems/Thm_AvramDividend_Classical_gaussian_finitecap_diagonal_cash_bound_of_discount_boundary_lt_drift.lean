-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_finitecap_diagonal_cash_bound_of_discount_boundary_lt_drift
-- name    : AvramDividend.Classical.gaussian_finitecap_diagonal_cash_bound_of_discount_boundary_lt_drift
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T06:43:17.616107+00:00
-- url     : https://prove2.me/theorems/d6e4d464-0ce5-506d-83e4-ea1b40d7596a
-- title:
--   Gaussian finite-cap Stieltjes cash bound when drift exceeds the discounted boundary value
-- statement:
--   For the original bounded-horizon dividend problem with a Gaussian-only source $\nu=0$, take a positive finite dividend cap and positive initial reserve. Assume the corrected boundary, generator, gradient, and dividend-jump hypotheses. In the regime where the constant drift $c$ exceeds $q w(0)$, prove that the expected discounted Stieltjes dividend cash through the original ruin clock clipped at the positive integer horizon $n$ is at most $w(x)$.
--
--   The same horizon $n$ is used in both payment-time restrictions. The estimate retains the original dividend measure, including its time-zero atom. It asks for the cash bound alone. When $c\le q w(0)$, the affine candidate $w(0)+y$ on the nonnegative half-line gives a separate route through the proved infinite-cap Gaussian estimate.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4 and (5.13), https://arxiv.org/pdf/math/0702893#page=19. Gaussian finite-cap diagonal stopped cash subcase of corrected theorem 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_finitecap_diagonal_cash_bound_of_discount_boundary_lt_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hDrift : q * w 0 < X.c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
