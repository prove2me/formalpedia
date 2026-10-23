-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_weighted_integral_zero_continuous
-- name    : AvramDividend.Classical.positive_weighted_integral_zero_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T21:09:15.176527+00:00
-- url     : https://prove2.me/theorems/b5771f1f-2f99-42d7-8357-0efd302524e5
-- title:
--   A continuous nonnegative function with zero finite weighted integral vanishes everywhere on the interval
-- statement:
--   If a function f is continuous and nonnegative on (0,∞), and exp(-θx)f(x) is integrable with zero integral over (0,R], then f(x)=0 at every point x∈(0,R]. First use the pinned Mathlib equivalence between zero Bochner integral of an a.e. nonnegative function and ae equality to zero, then upgrade to pointwise equality by Measure.eqOn_of_ae_eq (Lebesgue volume is open-positive and Ioc0R is contained in the closure of its interior). Since exp(-θx)>0, the original f must vanish. Supports the finite-horizon weighted-contraction proof of causal Volterra uniqueness.
-- source:
--   Pinned Mathlib integral_eq_zero_iff_of_nonneg_ae; Measure.eqOn_of_ae_eq; Ioc_subset_closure_interior

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.positive_weighted_integral_zero_continuous
    (f : ℝ → ℝ) (θ R : ℝ)
    (hfcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hfn : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hInt : IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) * f x)
      (Ioc (0 : ℝ) R) volume)
    (hzero : (∫ x in Ioc (0 : ℝ) R,
      Real.exp (-θ * x) * f x ∂volume) = 0) :
    ∀ x ∈ Ioc (0 : ℝ) R, f x = 0 := by sorry
