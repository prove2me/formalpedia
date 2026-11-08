-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_localised_mean_zero_budget_implies_expected_upper
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_localised_mean_zero_budget_implies_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:34:38.254411+00:00
-- url     : https://prove2.me/theorems/62955fef-6e16-4743-a24c-226713d1ffe8
-- title:
--   Original finite-cap stopped signed-martingale budgets imply every local expected upper and its limit
-- statement:
--   Assuming for each source-exact finite-cap stopped Fk an integrable centred martingale witness dominating the original payoff up to initial w(x), prove every expected upper bound by integration and prove the limiting expected upper bound under explicitly assumed almost-everywhere convergence. Source cash is the inclusive stopped dividend lintegral, and the proof derives Fk integrability from the published finite-cap envelope. This isolates the missing Ito-Meyer stochastic identity from deterministic expectation and limit transfer, without assuming the desired upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_localised_mean_zero_budget_implies_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hCashτI : Integrable
      (fun ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ (L : Ω → ℝ),
      (∀ k, AEStronglyMeasurable (F k) P) →
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (L ω))) →
      (∀ k, ∃ M : Ω → ℝ,
        Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂P, F k ω ≤ w x + M ω)) →
      (∀ k, (∫ ω, F k ω ∂P) ≤ w x) ∧
        (∫ ω, L ω ∂P) ≤ w x := by sorry
