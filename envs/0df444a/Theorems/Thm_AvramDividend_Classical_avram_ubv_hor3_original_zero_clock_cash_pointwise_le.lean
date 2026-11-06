-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_cash_pointwise_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_cash_pointwise_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:18:49.105717+00:00
-- url     : https://prove2.me/theorems/88f472ea-61fd-45bb-8c9c-a21c9603694f
-- title:
--   Pathwise original instantaneous-ruin stopped Stieltjes Cash is at most the initial HJB value
-- statement:
--   For every actual original spectrally negative Levy path and original capped admissible dividend strategy, a stopped clock equal to zero has exact real discounted Stieltjes Cash bounded by the initial HJB value, including its initial right-payment atom. The result holds pointwise, with no almost-everywhere exceptional set, and does not require unbounded variation, standing stochastic integration or a positive deterministic horizon. The proof uses all-cap HJB payoff nonnegativity, exact stopped terminal positivity and the original zero-clock dividend ledger.
-- source:
--   Public Proved a2629a86 pathwise zero-clock Cash+Term bound, 79db013c source interior gradient to capped payoff nonnegativity, and 42338799 exact original stopped discounted Term nonnegativity. This closes the actual instantaneous-ruin event pathwise before positive-clock Ito centring.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_terminal_nonnegative_of_cap_payoff_sign
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_cash_pointwise_le
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
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (ω : Ω) (hZero : τ ω = 0) :
    Cash ω ≤ w x := by sorry
