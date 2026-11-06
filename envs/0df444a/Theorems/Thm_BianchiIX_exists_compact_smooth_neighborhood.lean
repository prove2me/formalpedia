-- Prove2me | Theorems.Thm_BianchiIX_exists_compact_smooth_neighborhood
-- name    : BianchiIX.exists_compact_smooth_neighborhood
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:59:09.191998+00:00
-- url     : https://prove2.me/theorems/2970337c-7acd-4cc6-809f-8328b18b2130
-- title:
--   Smooth germs on a compact set give a uniform neighborhood and Lipschitz bound
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$
--   a real normed space, $S\subset E$ compact, $P$ a predicate on $E$,
--   and $f:E\to F$. Suppose each $x\in S$ has a neighborhood where
--   $P(y)$ holds and $f$ is $C^2$ at $y$. Then there are $\delta>0$ and
--   $C\geq1$ such that, whenever $x\in S$ and $\|y-x\|\leq\delta$,
--   $$P(y),\qquad f\text{ is }C^2\text{ at }y,\qquad
--   \|f(y)\|\leq C,\qquad \|f(y)-f(x)\|\leq C\|y-x\|.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactSmoothNeighborhood.lean#L10-L42

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Thickening

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

theorem BianchiIX.exists_compact_smooth_neighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS : IsCompact S) {P : E → Prop} {f : E → F}
    (hreg : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, P y ∧ ContDiffAt ℝ 2 f y) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ x ∈ S, ∀ y : E, ‖y - x‖ ≤ δ →
      P y ∧ ContDiffAt ℝ 2 f y ∧ ‖f y‖ ≤ C ∧ ‖f y - f x‖ ≤ C * ‖y - x‖ := by sorry
