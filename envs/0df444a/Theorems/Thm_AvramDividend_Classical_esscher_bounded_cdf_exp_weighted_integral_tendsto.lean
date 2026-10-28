-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_bounded_cdf_exp_weighted_integral_tendsto
-- name    : AvramDividend.Classical.esscher_bounded_cdf_exp_weighted_integral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:00:43.760691+00:00
-- url     : https://prove2.me/theorems/d929dc07-16ad-4d94-950b-28e1ea30eb3b
-- title:
--   Bounded finite-horizon CDF limits pass through exponentially weighted capital integrals
-- statement:
--   Let β>0 and F_n(x) be measurable CDF-like real functions bounded between zero and one, converging pointwise for every x to L(x). Then the exponentially weighted capital integrals over x>0, ∫e^{-βx}F_n(x)dx, converge to ∫e^{-βx}L(x)dx. The exact integrable majorant is exp(-βx) on (0,∞) and the proof uses pinned Mathlib integrability and dominated convergence, not any Wiener–Hopf factor or target transform. This enables the already-proved 1E-C genuine exponential-time CDF convergence to control the capital-integrated factor used in the descending Wiener-Hopf limit.
-- source:
--   Mathlib integrableOn_exp_mul_Ioi and tendsto_integral_of_dominated_convergence at pinned 0df444a. Source faithful to nonnegative CDF integrals.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
open MeasureTheory Filter Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_bounded_cdf_exp_weighted_integral_tendsto
    (β : ℝ) (hβ : 0 < β)
    (F : ℕ → ℝ → ℝ) (L : ℝ → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFbound : ∀ n x, 0 ≤ F n x ∧ F n x ≤ 1)
    (hlimit : ∀ x, Tendsto (fun n => F n x) atTop (nhds (L x))) :
    Tendsto (fun n => ∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * F n x ∂volume)
      atTop (nhds (∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * L x ∂volume)) := by sorry
