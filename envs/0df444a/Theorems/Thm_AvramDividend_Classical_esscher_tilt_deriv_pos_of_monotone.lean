-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilt_deriv_pos_of_monotone
-- name    : AvramDividend.Classical.esscher_tilt_deriv_pos_of_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:22:57.862084+00:00
-- url     : https://prove2.me/theorems/7d97d65d-e2f6-4e30-bb71-0570d70b7af3
-- title:
--   Strict positivity of the derivative of a positive exponentially tilted monotone scale factor
-- statement:
--   If θ>0 and G is differentiable and nondecreasing on the nonnegative axis with G(a)>0 at a>0, then the derivative of e^(θx)G(x) at a is strictly positive. By the preceding product rule it equals e^(θa)(θG(a)+G'(a)), where both factors are strictly positive because G'(a)≥0. This gives the reusable real-analysis component for proving positive W^(q)'(a) from an Esscher factorisation, independently of the barrier dividend value theorem.
-- source:
--   Esscher factorisation W^(q)(x)=exp(Φ(q)x)W_Φ(x), MDPI Risks 2019 7(4)121 equation (25); monotonicity and positivity of tilted q=0 scale functions; elementary calculus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilt_deriv_pos_of_monotone
    (θ a : ℝ) (hθ : 0 < θ) (ha : 0 < a)
    (G : ℝ → ℝ) (hGmon : MonotoneOn G (Set.Ici 0))
    (hGpos : 0 < G a) (hGdiff : DifferentiableAt ℝ G a) :
    0 < deriv (fun x : ℝ => Real.exp (θ * x) * G x) a := by sorry
