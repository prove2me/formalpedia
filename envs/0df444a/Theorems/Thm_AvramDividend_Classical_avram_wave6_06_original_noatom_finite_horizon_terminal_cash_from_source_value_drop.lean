-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_noatom_finite_horizon_terminal_cash_from_source_value_drop
-- name    : AvramDividend.Classical.avram_wave6_06_original_noatom_finite_horizon_terminal_cash_from_source_value_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:02:43.528815+00:00
-- url     : https://prove2.me/theorems/81efc495-c708-4eec-835e-89eca5ea089c
-- title:
--   Actual original finite-clock discounted prepayment terminal plus complete dividends from explicit source value-loss expectation
-- statement:
--   For original X and admissible left-continuous D, bounded right-continuous-filtration stopping time τ≤σ, zero-or-strict-preruin a.e., and no right dividend atom at the terminal clock, the actual prepayment riskProcess terminal discounted w plus the exact full inclusive original stopped Stieltjes dividend cash has ENNReal expectation bounded by ofReal(w x), provided one explicit source expected caplinear-value-loss budget holds. The latter is an honest unproved stochastic premise; this theorem does not assert the mixed controlled Ito-Meyer rule. At positive ruin crossings or right atoms, the stated terminal identification cannot be made.
-- source:
--   Avram Proposition 4(i), original stopped finite-horizon expected terminal and full dividends. Composes Proved c61d10df exact source-path ENNReal signed cash/value drop with a stated source-value expectation bound and a.e. no-right-terminal-dividend-atom alignment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_noatom_finite_horizon_terminal_cash_from_source_value_drop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 < q) (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_pos : ∀ y : ℝ, 0 < y → 0 ≤ w y)
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (hPre : ∀ᵐ ω ∂P, τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (hNoAtom : ∀ᵐ ω ∂P, rightLimit D (τ ω) ω = D (τ ω) ω)
    (hSourceValueBudget :
      (∫⁻ ω,
        ENNReal.ofReal
          (Real.exp (-(q * (τ ω : ℝ))) *
           w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) +
        ENNReal.ofReal
          (V (x + X.X (τ ω) ω) -
           V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) ∂P) ≤
      ENNReal.ofReal (w x)) :
    (∫⁻ ω,
      ENNReal.ofReal
        (Real.exp (-(q * (τ ω : ℝ))) *
         w (riskProcess X x D (τ ω) ω)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
