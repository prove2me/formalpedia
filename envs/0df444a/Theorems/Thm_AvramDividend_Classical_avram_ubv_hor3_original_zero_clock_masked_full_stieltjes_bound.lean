-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_masked_full_stieltjes_bound
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_masked_full_stieltjes_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:25:39.245867+00:00
-- url     : https://prove2.me/theorems/431785fe-f429-47a5-88a2-c30244fef2af
-- title:
--   Exact original zero-clock stopped discounted dividend-measure mass bounded in ENNReal expectation
-- statement:
--   For the original spectrally negative Levy X and original capped admissible D, the full raw ENNReal discounted Stieltjes dividend-measure integral on the actual zero stopping-clock event is bounded by the same event's initial HJB value. This controls the literal canonical paymentTimes and Iic stopped cash without relying on toReal conversion of a potentially infinite ENNReal integral, preserves the initial right dividend atom and is pointwise-founded rather than a proxy law. It is the source-exact immediate ruin component of positive-horizon UBV verification.
-- source:
--   Proved public zero-horizon raw Stieltjes identity 1fb597ac, original dividendMeasure singleton identity 4f229f9a, the exact original real stopped initial atom 5514c6b0, original admissible dividend right-limit nonnegativity and HOR3 pointwise zero-clock HJB cash bound 88f472ea. Bridge: raw source lintegral equals finite ENNReal.ofReal Cash on zero clock, then pointwise bound under zero event and lintegral_mono.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_cash_pointwise_le
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_masked_full_stieltjes_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
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
    (∫⁻ ω, if τ ω = 0 then
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if τ ω = 0 then ENNReal.ofReal (w x) else 0 ∂P) := by sorry
