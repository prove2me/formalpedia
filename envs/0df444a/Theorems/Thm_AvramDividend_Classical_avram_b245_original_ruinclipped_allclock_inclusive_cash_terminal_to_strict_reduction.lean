-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b245_original_ruinclipped_allclock_inclusive_cash_terminal_to_strict_reduction
-- name    : AvramDividend.Classical.avram_b245_original_ruinclipped_allclock_inclusive_cash_terminal_to_strict_reduction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:25:40.949553+00:00
-- url     : https://prove2.me/theorems/e91a532d-b6fb-4115-a987-081d496c10cd
-- title:
--   Original ruin-clipped mixed all-stop inclusive Iic cash and terminal contact reduced to zero-clock budget or strict prepayment terminal risk value
-- statement:
--   For the original B236 F with inclusive Iic dividend cash and correct pre-ruin versus ruin terminal reserve, if the initial zero-clock cash is bounded by w(x), then for every original stopping clock sigma the full F is bounded by w(x) on sigma=0 and otherwise by the true discounted terminal riskProcess value plus genuinely strict Iio(sigma) dividend cash. This captures both time-zero right payments and the possible ruin-time terminal contact without sampling the process after ruin, providing a clean final-condition reduction for the physical Itô–Meyer source ledger. The required zero-clock budget is already Proved independently for the original B236 hypotheses.
-- source:
--   Case split on the genuine original stopping clock. Zero branch uses the supplied exact original zero-clock w(x) upper bound; positive branch applies Proved B244 inclusive-to-strict right-payment terminal contact inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b245_original_ruinclipped_allclock_inclusive_cash_terminal_to_strict_reduction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
            (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hZero : ∀ ω, σ ω = 0 → F ω ≤ w x) :
    ∀ ω, F ω ≤
      if σ ω = 0 then w x
      else Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
