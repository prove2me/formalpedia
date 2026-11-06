-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_masked_ennreal_cash_bound
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_masked_ennreal_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:10:18.91688+00:00
-- url     : https://prove2.me/theorems/171e4064-6269-4346-9398-bd25dc98a211
-- title:
--   Original UBV zero-clock event carries at most the initial HJB value in masked expected Stieltjes Cash
-- statement:
--   For the original unbounded-variation Levy X and original capped admissible D, the full discounted Stieltjes Cash contribution on exactly zero stopping-clock paths is bounded as an ENNReal outer expectation by the same event's initial HJB value. Both integrals preserve the zero-time right-dividend atom. The result combines the original zero-clock pathwise terminal/Cash budget with an independent source terminal sign, and remains valid when the deterministic horizon is positive but immediate ruin occurs.
-- source:
--   From accepted public original-source zero-clock theorem a2629a86 and public source terminal nonnegativity theorem 18481770; bridge: nonnegative Term permits Cash<=w(x) on the zero-clock event and ENNReal lintegral monotonicity. No source Ito martingale or proxy law is assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_exact_zero_or_preruin_terminal_nonnegative
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_masked_ennreal_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    (∫⁻ ω, if τ ω = 0 then ENNReal.ofReal (Cash ω) else 0 ∂P) ≤
      (∫⁻ ω, if τ ω = 0 then ENNReal.ofReal (w x) else 0 ∂P) := by sorry
