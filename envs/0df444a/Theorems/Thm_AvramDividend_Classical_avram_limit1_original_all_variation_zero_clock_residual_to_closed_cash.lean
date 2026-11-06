-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_all_variation_zero_clock_residual_to_closed_cash
-- name    : AvramDividend.Classical.avram_limit1_original_all_variation_zero_clock_residual_to_closed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:51:13.413623+00:00
-- url     : https://prove2.me/theorems/ab5d51c0-1d66-4986-af64-465f1002b0b3
-- title:
--   Source-exact all-BV/UBV, zero-clock single residual bounds actual closed Stieltjes cash
-- statement:
--   For the original capped admissible dividend strategy at any nonnegative reserve, use an actual finite stopped ruin clock and original postpayment W, real Cash and Term. If source-exact integrable centred martingale M, integrable drift remainders G,H with G+H≤0 and stopped Itô-Dynkin residual Term+Cash≤w(x)+M+G+H are supplied, the genuinely closed Iic(τ) ENNReal dividendMeasure expectation is bounded by ENNReal.ofReal(w x). Unlike the older UBV-only residual-to-stopped-cash bridge, this works uniformly for BV C1 and UBV C2 smoothness and exact τ=0 right-payment branch, and requires neither terminal integrability nor terminal vanishing. The missing stochastic residual remains an explicit premise.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_limit1_original_exact_zero_clock_terminal_nonnegative_bv_ubv
import Theorems.Thm_AvramDividend_Classical_avram_limit1_bounded_clock_stopped_residual_to_ennreal_cash

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_original_all_variation_zero_clock_residual_to_closed_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hSource : ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        w x + M ω + G ω + H ω)) :
    (∫⁻ ω, ∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry
