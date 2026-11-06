-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_full_cash_budget
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_full_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:57:04.665644+00:00
-- url     : https://prove2.me/theorems/8c5aee33-8b34-4c09-b845-ff85affc496f
-- title:
--   Original positive bounded-clock immediate-ruin complete Stieltjes expectation bound
-- statement:
--   At every positive natural clipped ruin clock and nonnegative deterministic horizon, the literal original discounted Stieltjes dividend payout on the zero stopped-clock event is bounded by the corresponding event-masked initial HJB value. On immediate ruin, paymentTimes for the bounded natural clock contributes precisely the source time-zero right-dividend atom at any T≥0. This uses the original X and D, rather than a surrogate process, and carries the exact raw ENNReal integral to the positive-clock verification split.
-- source:
--   Independent zero-clock branch: Proved original finite-clock zero iff immediate ruin c28dcd9b and source-exact HOR3 zero-clock raw Stieltjes bound 431785fe. Under ruinTime=0, paymentTimes(min ruinTime n) has only the initial singleton payment; T≥0 retains it and the canonical source Cash domain ends at stopped time zero. Full event-masked lintegral equality followed by accepted masked bound. No stochastic source or P4-F residual imported.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_horizon_zero_clock_iff_immediate_ruin
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_masked_full_stieltjes_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_ruin_bounded_horizon_masked_full_cash_budget
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
    (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (W Cash Term : Ω → ℝ)
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
      (∫⁻ s in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, if τ ω = 0 then ENNReal.ofReal (w x) else 0 ∂P) := by sorry
