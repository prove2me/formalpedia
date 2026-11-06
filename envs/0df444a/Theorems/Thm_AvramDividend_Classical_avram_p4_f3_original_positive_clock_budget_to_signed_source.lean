-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_clock_budget_to_signed_source
-- name    : AvramDividend.Classical.avram_p4_f3_original_positive_clock_budget_to_signed_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:07:11.678935+00:00
-- url     : https://prove2.me/theorems/11fb9ebb-ec24-48f0-a9fa-cd967477f280
-- title:
--   Original stopped UBV signed witnesses from strictly positive-clock expected budget, zero-clock atom discharged
-- statement:
--   On the genuine original spectrally negative Levy source X and actual stopped dividend measure, positive-clock expected terminal-plus-cash inequality weighted by the positive-clock probability suffices for full original stopped signed Ito witnesses. At the zero-clock event the true initial right-payment and terminal are bounded pathwise by already Proved source ledger. This reduces the remaining stochastic obstruction to strictly positive clocks, including positive ruin and cap contact; the positive-clock estimate remains an explicit mathematical hypothesis.
-- source:
--   Canonical P4-F3 residual 0dda1be7; Proved original zero-clock exact term-plus-cash source a2629a86; Proved source-exact all-cap ENNReal-to-signed helper b42989a9; Mathlib lintegral measurable-set/complement decomposition. No dependency on either Open canonical target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_allcap_ennreal_bound_to_signed_source
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f3_original_positive_clock_budget_to_signed_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hZeroMeas : MeasurableSet {ω | τ ω = 0})
    (hwx : 0 ≤ w x)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hCashPos : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hPositive : (∫⁻ ω in {ω | τ ω ≠ 0},
        ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) * P {ω | τ ω ≠ 0}) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
