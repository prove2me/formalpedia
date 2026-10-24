-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact
-- name    : FiniteEnergyPlane.exists_lipschitz_near_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-23T16:55:34.613087+00:00
-- url     : https://prove2.me/theorems/b5a84551-2740-462f-9068-c5a1f9826624
-- title:
--   Uniform bound and Lipschitz constant of a $C^1$ map on balls of fixed radius around a compact set
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, $O\subseteq E$ open, $f:E\to F$ of class $C^1$ on $O$, and $K\subseteq O$ compact. Then there are $\delta>0$ and $D\ge0$ such that for every $p\in K$:
--   - the closed ball $\bar B(p,\delta)$ is contained in $O$;
--   - $\|f(y)\|\le D$ for all $y\in\bar B(p,\delta)$;
--   - $\|f(y)-f(y')\|\le D\,\|y-y'\|$ for all $y,y'\in\bar B(p,\delta)$.
--
--   **Role.** Uniform size and Lipschitz constants for a $C^1$ coefficient field (such as an almost complex structure) on balls of a fixed radius centred anywhere in a compact set; used for estimates uniform in the centre point.
-- source:
--   Standard (mean value inequality)

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

namespace FiniteEnergyPlane

open Metric Set

/-- Uniform bounds near a compact set. Let `f` be a `C¹` map on an open subset `O` of a
finite-dimensional real normed space and `K ⊆ O` compact. There are `δ > 0` and `D ≥ 0` such
that for every `p ∈ K` the closed ball `closedBall p δ` lies in `O`, `‖f y‖ ≤ D` on it, and `f` is
`D`-Lipschitz on it. -/
theorem exists_lipschitz_near_compact {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {O : Set E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ 1 f O) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ > 0, ∃ D, 0 ≤ D ∧ ∀ p ∈ K, closedBall p δ ⊆ O ∧
      ∀ y ∈ closedBall p δ, ‖f y‖ ≤ D ∧ ∀ y' ∈ closedBall p δ, ‖f y - f y'‖ ≤ D * ‖y - y'‖ := by
  sorry

end FiniteEnergyPlane
