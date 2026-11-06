-- Prove2me | Theorems.Thm_BianchiIX_exists_compact_vanishing_slice_bounds
-- name    : BianchiIX.exists_compact_vanishing_slice_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T06:48:26.598101+00:00
-- url     : https://prove2.me/theorems/6ae9981a-adb8-49f6-aa6a-dca7b7aa78f5
-- title:
--   Vanishing on a compact slice controls values and tangential derivatives
-- statement:
--   Let $E,F$ be finite-dimensional real normed spaces,
--   $V$ a real normed space, $K\subset F$ compact, and $f:E\times F\to V$.
--   Suppose $f$ is $C^2$ at every $(0,x)$ with $x\in K$, and $f(0,x)=0$
--   for every $x\in F$. There exist $\delta>0$ and $C\geq1$ such that,
--   for $x\in K$ and $\|u\|\leq\delta$, $f$ is $C^2$ at $(u,x)$ and
--   $$\|f(u,x)\|\leq C\|u\|,\quad \|df_{(u,x)}\|\leq C,\quad
--   \|df_{(u,x)}(0,w)\|\leq C\|u\|\|w\|\quad(w\in F).$$
--   The product carries the maximum norm.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/CompactVanishingSlice.lean#L11-L78

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

theorem BianchiIX.exists_compact_vanishing_slice_bounds
    {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : E × F → V} {K : Set F} (hK : IsCompact K)
    (hreg : ∀ x ∈ K, ContDiffAt ℝ 2 f (0, x)) (hzero : ∀ x : F, f (0, x) = 0) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ x ∈ K, ∀ u : E, ‖u‖ ≤ δ →
      ContDiffAt ℝ 2 f (u, x) ∧ ‖f (u, x)‖ ≤ C * ‖u‖ ∧
      ‖fderiv ℝ f (u, x)‖ ≤ C ∧
      ∀ w : F, ‖fderiv ℝ f (u, x) (0, w)‖ ≤ C * ‖u‖ * ‖w‖ := by sorry
