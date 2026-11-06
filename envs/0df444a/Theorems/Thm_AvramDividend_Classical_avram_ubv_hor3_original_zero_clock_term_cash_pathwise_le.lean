-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:10:40.77393+00:00
-- url     : https://prove2.me/theorems/a2629a86-d97d-4ba4-8aef-18371fa6b5cf
-- title:
--   Actual original zero-stopping-clock discounted terminal plus Stieltjes Cash is pathwise below initial HJB value
-- statement:
--   For the actual spectrally negative Levy X and an original admissible dividend strategy, any stopped clock tau that equals zero on a sample path has exact discounted Term plus full original stopped real Stieltjes Cash bounded above by w(x). The proof uses the physical initial right-dividend jump, zero-clock W/Term identity, original Stieltjes atom and the original HJB jump inequality. It does not assume positive ruin time, introduce a proxy process, or use stochastic centring. This is the explicit degenerate-clock branch for strictly positive-horizon UBV Ito verification.
-- source:
--   Original source proof from public Proved 5514c6b0, 858cdf8b, e6bfefd9 and dividendStrategy_le_rightLimit. All variables are literal original X, D, ruinTime, W, Cash, Term; terminal and initial cash atoms are retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_zero_clock_real_cash_eq_initial_rightatom
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_zero_clock_rightpayment_term_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_zero_atom_postpayment_ledger_entry
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
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
    Term ω + Cash ω ≤ w x := by sorry
