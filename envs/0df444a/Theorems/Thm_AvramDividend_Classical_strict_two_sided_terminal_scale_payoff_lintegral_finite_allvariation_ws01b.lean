-- Prove2me | Theorems.Thm_AvramDividend_Classical_strict_two_sided_terminal_scale_payoff_lintegral_finite_allvariation_ws01b
-- name    : AvramDividend.Classical.strict_two_sided_terminal_scale_payoff_lintegral_finite_allvariation_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:30:28.865838+00:00
-- url     : https://prove2.me/theorems/24987cfd-342c-4d63-ae7c-760b6f523f99
-- title:
--   Finite strict two-sided terminal scale expectation for every spectrally negative Lévy variation regime
-- statement:
--   Unify the bounded-variation and unbounded-variation accepted terminal-scale integrability theorems into a single result without variation assumptions. The full discounted strict two-sided q-scale terminal reward has finite expectation at nonnegative starting reserve x≤a and q>0. The proof uses classical case analysis on bounded variation, preserving the positive boundary value Wq(0) where applicable.
-- source:
--   Canonical Prove2Me bounded-variation and unbounded-variation strict two-sided terminal q-scale integrability results.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_bv_strict_two_sided_terminal_scale_payoff_lintegral_finite_ws01b
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_terminal_scale_payoff_lintegral_finite_unbounded

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.strict_two_sided_terminal_scale_payoff_lintegral_finite_allvariation_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      (if twoSidedExitUpTime X (a - x) ω <
           twoSidedExitDownTime X (-x) ω then
         ENNReal.ofReal
           (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
           ENNReal.ofReal
             (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
       else 0) +
      (if twoSidedExitDownTime X (-x) ω <
           twoSidedExitUpTime X (a - x) ω then
         ENNReal.ofReal
           (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
           ENNReal.ofReal
             (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
       else 0) ∂P) < ⊤ := by sorry
