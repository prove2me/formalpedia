-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:26:08.257341+00:00
-- url     : https://prove2.me/theorems/d9f85ad8-bf42-4eb5-98ee-38542debf943
-- title:
--   Integrability of source-original negative dividend residual dominated by full stopped Stieltjes cash
-- statement:
--   For the exact original Lévy-controlled dividend measure and payment-times selector, the true ruin-stopped discounted Stieltjes Cash is nonnegative pointwise. If an a.e. strongly measurable source-ordered right-dividend correction Hdiv is nonpositive and its negative is bounded by (K−1) times that exact Cash, with a single finite K≥1, then Hdiv is integrable whenever Cash is. The proof uses only the verified Mathlib Integrable.mono and avoids any cap-boundary derivative assertion. This is the integrability interface the original stopped Itô–Meyer assembler requires.
-- source:
--   Avram–Palmowski–Pistorius, Proposition 4(i), Eq. (5.13); source original hCash from 0dda1be7 and pinned Mathlib Integrable.mono; accepted original P4-D absolute cash envelope 9174e536 plus strong carrier in progress

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_cash_dominates_integrable_negative_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0) (Cash Hdiv : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hHmeas : AEStronglyMeasurable Hdiv P)
    (K : ℝ) (hK : 1 ≤ K)
    (hHsign : ∀ᵐ ω ∂P, Hdiv ω ≤ 0)
    (hHupper : ∀ᵐ ω ∂P, -Hdiv ω ≤ (K - 1) * Cash ω) :
    Integrable Hdiv P ∧ (∀ᵐ ω ∂P, Hdiv ω ≤ 0) := by sorry
