-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_single_centered_source_nat_horizon_cash_budget
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_single_centered_source_nat_horizon_cash_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:26:14.067697+00:00
-- url     : https://prove2.me/theorems/da53a9bf-263d-4f62-9146-4aaabc1ab11f
-- title:
--   Original stopped finite-horizon dividend cash budget from a single physical centred martingale and nonintegrable signed remainder
-- statement:
--   For the same original spectrally negative Levy X, true dividend process D, stopped ruin clock, piecewise terminal W, exact closed-horizon Stieltjes Cash, and discounted Term, one integrable centred source martingale M plus an almost-surely nonpositive signed remainder R with the genuine stopped Ito-Meyer source upper inequality suffices to bound expected cash over every closed Iic T horizon by ENNReal.ofReal(w x). No integrability of R and no split component martingales are required. The physical source inequality is explicitly a hypothesis, not asserted as proved.
-- source:
--   Full formal reduction for UBV-HOR3 using independently Proved 967f4fb9 actual-stopped cash expectation conversion and Proved truncated_cash_le_actual_stopped_clock. Imports no canonical d457, 665, fdb, 0dda or SWEEP16 target. It isolates the single genuine missing stochastic source inequality and preserves original measure/ruin/horizon atoms.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_stopped_cash_from_measurable_ito_data
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_truncated_cash_le_actual_stopped_clock
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_single_centered_source_nat_horizon_cash_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (T : ℝ) (τ : Ω → ℝ≥0)
    (hτEq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτStop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term M R : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hMI : Integrable M P) (hMzero : (∫ ω, M ω ∂P) = 0)
    (hRnonpos : ∀ᵐ ω ∂P, R ω ≤ 0)
    (hSource : ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + R ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
