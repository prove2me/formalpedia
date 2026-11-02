-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isJHolomorphicOn_comp_of_differentiableAt
-- name    : FiniteEnergyPlane.isJHolomorphicOn_comp_of_differentiableAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T10:30:43.73722+00:00
-- url     : https://prove2.me/theorems/2932c295-92f3-41fd-8edb-b51306e92304
-- title:
--   Holomorphic reparametrizations preserve pseudoholomorphic maps
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $J:E\to\mathrm{End}(E)$, and let $g:\mathbb{C}\to E$ be $J$-holomorphic on $U\subseteq\mathbb{C}$, i.e. differentiable with $\partial_sg+J(g)\partial_tg=0$ there, with $J(g(z))^2=-1$ for $z\in U$. If $f:\mathbb{C}\to\mathbb{C}$ is complex differentiable at every point of $W$ and $f(W)\subseteq U$, then $g\circ f$ is $J$-holomorphic on $W$.
--
--   This lets pseudoholomorphic curves be read in any holomorphic coordinate, e.g. $z\mapsto z^{-1}$ near $\infty$.
--
--   **Formalization Note** $J$-holomorphic is `JHolomorphic.IsJHolomorphicOn`; no openness of $U$ or $W$ is assumed.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 (case of planes)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Holomorphic changes of variables preserve `J`-holomorphicity: if `g` is `J`-holomorphic on
`U`, `J(g z)² = -1` for `z ∈ U`, and `f` is complex differentiable at every point of `W` with
`f(W) ⊆ U`, then `g ∘ f` is `J`-holomorphic on `W`. -/
theorem isJHolomorphicOn_comp_of_differentiableAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (U W : Set ℂ) (g : ℂ → E)
    (hg : JHolomorphic.IsJHolomorphicOn J U g)
    (hJ : ∀ z ∈ U, (J (g z)).comp (J (g z)) = -ContinuousLinearMap.id ℝ E) (f : ℂ → ℂ)
    (hf : ∀ z ∈ W, DifferentiableAt ℂ f z ∧ f z ∈ U) :
    JHolomorphic.IsJHolomorphicOn J W (fun z => g (f z)) := by
  sorry

end FiniteEnergyPlane
