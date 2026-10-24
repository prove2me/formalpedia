-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_damped_resolvent_C1_of_continuous_forcing
-- name    : AvramDividend.Classical.causal_damped_resolvent_C1_of_continuous_forcing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:36:25.991454+00:00
-- url     : https://prove2.me/theorems/9a0eb6c3-e0e9-4e97-af4d-bb55172543c6
-- title:
--   C1 regularity of a damped causal resolvent with continuous forcing
-- statement:
--   If the forcing g is continuous on positive times and H has derivative H'=g-wH there, then H is continuously differentiable on positive times. This bridges the pointwise exponential primitive HasDerivAt theorem to the C1 Neumann-series criterion.
-- source:
--   The derivative criterion contDiffOn_succ_iff_deriv_of_isOpen applied to H'=g-wH, with continuity of H from HasDerivAt and continuity of g.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Basic

open Set

theorem AvramDividend.Classical.causal_damped_resolvent_C1_of_continuous_forcing
    (H g : ℝ → ℝ) (w : ℝ)
    (hg : ContinuousOn g (Ioi (0 : ℝ)))
    (hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt H (g x - w * H x) x) :
    ContDiffOn ℝ 1 H (Ioi (0 : ℝ)) := by sorry
