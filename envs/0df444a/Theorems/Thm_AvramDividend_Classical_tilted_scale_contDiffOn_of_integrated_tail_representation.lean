-- Prove2me | Theorems.Thm_AvramDividend_Classical_tilted_scale_contDiffOn_of_integrated_tail_representation
-- name    : AvramDividend.Classical.tilted_scale_contDiffOn_of_integrated_tail_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T04:22:13.464393+00:00
-- url     : https://prove2.me/theorems/5f27b886-480e-4910-9cc1-2764fd74b32b
-- title:
--   Tilted scale C1 from integrated excursion-tail representation
-- statement:
--   If a function W satisfies an integrated exponential representation with a continuous tail rate on the positive half-line, then W is continuously differentiable there, and the Esscher-tilted function V(x)=exp(-phi*x)*W(x) is also continuously differentiable there. This isolates the deterministic analytic leg of unbounded_tilted_scale_absolute_continuity: the remaining stochastic content is deriving the continuous-tail representation from the scale function and unbounded variation.
-- source:
--   Parent 0883e459-3837-4637-80a5-754b764aebb6 (Open, unbounded_tilted_scale_absolute_continuity); analytic chain frozen in candidates/work_on/0883_WC1_from_repr_20261028ad.lean reusing ACCEPTED 5b518605, 5350cb84, bd041e71 patterns. Proved root e600b0a2-93ac-4ee2-b2c6-c087147d0b18 already covers branch-1 existence, so this child captures only the hcont+hexp to ContDiffOn V implication with no scale-function, bounded-variation, or root hypotheses.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.tilted_scale_contDiffOn_of_integrated_tail_representation
    (W : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0))
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t)))
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by sorry
