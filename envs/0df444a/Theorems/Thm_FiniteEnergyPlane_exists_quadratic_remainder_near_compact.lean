-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_quadratic_remainder_near_compact
-- name    : FiniteEnergyPlane.exists_quadratic_remainder_near_compact
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:49:00.559867+00:00
-- url     : https://prove2.me/theorems/345b173a-6d43-48de-9fdd-0e40dd04a5d1
-- title:
--   Uniform Lipschitz and quadratic Taylor bounds for a C² map near a compact set
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $F$ a real normed space, $O \subseteq E$ open, $f : O \to F$ of class $C^2$, and $K \subseteq O$ compact. Then there are $\delta > 0$ and $D \ge 0$ such that for every $p \in K$:
--   - the closed ball $\bar B(p, \delta)$ lies in $O$;
--   - $\|f(y) - f(y')\| \le D\,\|y - y'\|$ for all $y, y' \in \bar B(p, \delta)$;
--   - $\|f(y) - f(p) - Df(p)(y - p)\| \le D\,\|y - p\|^2$ for all $y \in \bar B(p, \delta)$.
--
--   Role: uniform first-order Taylor bounds near a compact set, for comparing trajectories of a smooth vector field with their linearization.
--
--   Formalization Note: $C^2$ on $O$ is `ContDiffOn ℝ 2 f O`; the derivative is `fderiv ℝ f p`.
-- source:
--   Standard (Taylor's theorem with mean-value remainder)

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

namespace FiniteEnergyPlane

open Metric Set

/-- Uniform first-order Taylor bounds near a compact set. Let `f` be a `C²` map on an open subset
`O` of a finite-dimensional real normed space and `K ⊆ O` compact. There are `δ > 0` and `D ≥ 0`
such that for every `p ∈ K` the closed ball `closedBall p δ` lies in `O`, `f` is `D`-Lipschitz on
it, and `‖f y - f p - Df(p)(y - p)‖ ≤ D ‖y - p‖²` for `y` in it. -/
theorem exists_quadratic_remainder_near_compact {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ 2 f O)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ > 0, ∃ D, 0 ≤ D ∧ ∀ p ∈ K, closedBall p δ ⊆ O ∧
      (∀ y ∈ closedBall p δ, ∀ y' ∈ closedBall p δ, ‖f y - f y'‖ ≤ D * ‖y - y'‖) ∧
      ∀ y ∈ closedBall p δ, ‖f y - f p - fderiv ℝ f p (y - p)‖ ≤ D * ‖y - p‖ ^ 2 := by
  sorry

end FiniteEnergyPlane
