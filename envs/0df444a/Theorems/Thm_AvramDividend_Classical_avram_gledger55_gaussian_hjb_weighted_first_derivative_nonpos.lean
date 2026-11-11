-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger55_gaussian_hjb_weighted_first_derivative_nonpos
-- name    : AvramDividend.Classical.avram_gledger55_gaussian_hjb_weighted_first_derivative_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:39:02.643406+00:00
-- url     : https://prove2.me/theorems/20f89327-30aa-4867-a790-a645a3749917
-- title:
--   Gaussian HJB weighted first derivative has nonpositive derivative on positive reserves
-- statement:
--   For positive Gaussian variance coefficient a and two characteristic roots r,l of the discounted Gaussian generator, the zero-jump HJB supersolution inequality makes the weighted first derivative exp(-r y)(w'(y)-l w(y)) nonincreasing. This is the exact deterministic factorisation step needed for the one-sided exponential envelope used to control the positive physical source in gledger53.
-- source:
--   Direct necessary analytic child for Open gledger53 (a604fe09), which remains an original-process stochastic positive-source integrability obligation. The ODE factorisation must be combined with characteristic-root existence and a first-order comparison bound before invoking it for source control.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger55_gaussian_hjb_weighted_first_derivative_nonpos
    (a b q r l : ℝ) (ha : 0 < a)
    (hlin : b = -a * (r + l)) (hprod : q = -a * r * l)
    (w : ℝ → ℝ)
    (hsmooth : ∀ y : ℝ, 0 < y →
      HasDerivAt w (deriv w y) y ∧
        HasDerivAt (deriv w) (iteratedDeriv 2 w y) y)
    (hode : ∀ y : ℝ, 0 < y →
      a * iteratedDeriv 2 w y + b * deriv w y - q * w y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      deriv (fun z => Real.exp (-(r * z)) * (deriv w z - l * w z)) y ≤ 0 := by sorry
