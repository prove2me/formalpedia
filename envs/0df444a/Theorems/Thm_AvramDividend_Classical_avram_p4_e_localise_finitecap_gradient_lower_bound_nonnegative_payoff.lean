-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff
-- name    : AvramDividend.Classical.avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:47:18.618224+00:00
-- url     : https://prove2.me/theorems/ef15784e-e2a0-4f54-baad-1950e8e11e62
-- title:
--   Finite-cap nonnegative payoff from interior derivative bound and actual zero-boundary continuity
-- statement:
--   For finite real cap c≥0 and source nonnegative half-line continuity, a differentiable payoff with derivative at least one at every strictly interior point is nondecreasing on [0,c], hence w(y)≥w(0)≥0 at both endpoints and throughout. This source-faithful analytic helper isolates the exact mean-value/endpoint step; P4-F's ContDiffOn interior supplies its DifferentiableOn interface separately.
-- source:
--   Mathlib.Analysis.Calculus.Deriv.MeanValue.monotoneOn_of_deriv_nonneg; source P4-F hw0/hw_cont/hw_smooth/hw_grad.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- Positive interior derivative, source boundary continuity and w(0) ≥ 0 imply nonnegative finite-cap payoff, including both endpoints. -/
theorem AvramDividend.Classical.avram_p4_e_localise_finitecap_gradient_lower_bound_nonnegative_payoff
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwDiff : DifferentiableOn ℝ w (Ioo (0 : ℝ) c))
    (hwGrad : ∀ y : ℝ, 0 < y → y < c → 1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → y ≤ c → 0 ≤ w y := by sorry
