-- Prove2me | Theorems.Thm_CauchyRiemannIndex_linearODE_continuous_param
-- name    : CauchyRiemannIndex.linearODE_continuous_param
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:12:44.955572+00:00
-- url     : https://prove2.me/theorems/a06a9f39-da53-405b-a4a2-22804befd9bf
-- title:
--   Joint continuity of solutions of linear ODEs depending continuously on a parameter
-- statement:
--   Let $X$ be a topological space and $E$ a real normed space. Let $B:X\times\mathbb R\to\mathcal L(E)$ be continuous for the operator norm, let $x_0:X\to E$ be continuous, and for each $\tau\in X$ let $x_\tau:\mathbb R\to E$ be differentiable with
--   $$x_\tau(0)=x_0(\tau),\qquad x_\tau'(t)=B(\tau,t)\,x_\tau(t)\quad\text{for all }t\in\mathbb R.$$
--   Then the map $X\times[0,1]\to E$, $(\tau,t)\mapsto x_\tau(t)$, is continuous.
--
--   This is continuous dependence of solutions of linear equations on a parameter, uniformly on a compact time interval. It is used for families of fundamental solutions $\Psi_\tau'=J_0S_\tau\Psi_\tau$ of continuous families of loops $S_\tau$.
--
--   **Formalization Note.** $B$ is a continuous map `X × ℝ → E →L[ℝ] E`; the solutions are given as `x : X → ℝ → E` with `HasDerivAt (x τ) (B (τ, t) (x τ t)) t` for all $\tau,t$. No completeness of $E$ and no compactness of $X$ is assumed. The conclusion is continuity on `X × unitInterval`.
-- source:
--   Standard continuous dependence of solutions of linear ODEs on parameters; e.g. P. Hartman, Ordinary Differential Equations, 2nd ed., SIAM 2002, Chapter V, Theorem 3.1

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Module.Basic

namespace CauchyRiemannIndex

open Filter Topology

/-- Continuous dependence on a parameter for linear equations: if `B(τ, t)` is a jointly
continuous family of bounded operators on a real normed space, `x₀(τ)` depends continuously on
`τ`, and `x τ` solves `x' = B(τ, t) x` with `x τ 0 = x₀ τ`, then `(τ, t) ↦ x τ t` is jointly
continuous on `X × [0, 1]`. -/
theorem linearODE_continuous_param {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : X × ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : X → E)
    (hx₀ : Continuous x₀) (x : X → ℝ → E) (hx0 : ∀ τ, x τ 0 = x₀ τ)
    (hx : ∀ τ t, HasDerivAt (x τ) (B (τ, t) (x τ t)) t) :
    Continuous (fun p : X × unitInterval => x p.1 p.2) := by
  sorry

end CauchyRiemannIndex
