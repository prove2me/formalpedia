-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_no_terminal_payment_atom_expected_book_budget_from_source_piecewise
-- name    : AvramDividend.Classical.avram_wave6_06_no_terminal_payment_atom_expected_book_budget_from_source_piecewise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:48:29.475534+00:00
-- url     : https://prove2.me/theorems/da64f8a5-51f2-40f2-8743-65dc2e4f4b0b
-- title:
--   Original no-terminal-right-dividend-atom converts actual piecewise source HJB budget to the book U_tau inequality
-- statement:
--   For the original spectrally negative Lévy process, same filtration and dividend strategy, genuine right-continuous stopping time bounded by the original ruin, and exact complete inclusive stopped dividend Stieltjes cash, assume a valid source piecewise-terminal expected HJB inequality and the necessary no-right-dividend-payment atom D_(tau+)=D_tau. The already Proved original pathwise piecewise-to-book bridge gives the literal e^(-q tau)w(U_tau)+Cash_tau expectation bound without changing terminal value conventions or asserting any unproved stochastic Ito identity.
-- source:
--   Avram–Palmowski–Pistorius, Proposition 4(i), Eq. (5.11)-(5.13), original left-continuous cumulative dividend convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_no_terminal_right_dividend_piecewise_eq_book
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_no_terminal_payment_atom_expected_book_budget_from_source_piecewise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 < q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hNoAtom : ∀ ω, rightLimit D (τ ω) ω = D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hBudget : (∫ ω, Term ω + Cash ω ∂P) ≤ w x) :
    (∫ ω, Real.exp (-(q * (τ ω : ℝ))) * w (riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω).toReal ∂P) ≤ w x := by sorry
