-- Prove2me | Theorems.Thm_ConformalBoundary_caratheodory_torhorst_exterior
-- name    : ConformalBoundary.caratheodory_torhorst_exterior
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T20:59:07.536202+00:00
-- url     : https://prove2.me/theorems/11721638-9338-49d8-9c92-7d6d80b208c9
-- title:
--   Carathéodory–Torhorst theorem, exterior form for a curve
-- statement:
--   Let $\gamma : [0,1] \to \mathbb C$ be continuous, with $K = \gamma([0,1])$ not a single point. Let $U$ be the set of points $z \notin K$ whose connected component in $\mathbb C \setminus K$ is unbounded (that is, the unbounded complementary component of $K$). Then there is $\Phi : \mathbb C \to \mathbb C$ that is continuous on $\{|w| \ge 1\}$, holomorphic and injective on $\{|w| > 1\}$, maps $\{|w| > 1\}$ onto $U$, and maps the unit circle onto the frontier of $U$. It is also not constant on any arc of the circle: for all real $\alpha < \beta$ some $\theta \in [\alpha, \beta]$ has $\Phi(e^{i\theta}) \ne \Phi(e^{i\alpha})$.
--
--   This is the classical theorem in its exterior form. Since $K$ is a Peano continuum, Torhorst's theorem makes the frontier of $U$ locally connected. Carathéodory's theorem (Pommerenke, Theorem 2.1) then extends the conformal map of $\{|w| > 1\}$ onto $U \cup \{\infty\}$, normalised by $\Phi(\infty) = \infty$, continuously to the closed exterior disk, and the extension maps the circle onto $\partial U$. A conformal map's boundary values cannot be constant on an arc, by the Schwarz reflection principle or the Riesz–Privalov uniqueness theorem. No normalisation at $\infty$ is part of the statement.
--
--   It is published as a leaf under `OuterplanarL1Tan.Linear.exists_outerFacialWalk_of_connected`, applied with $K$ the image of a connected plane graph drawing. The statement does not require $\gamma$ to be closed or injective.
-- source:
--   Ch. Pommerenke, Boundary Behaviour of Conformal Maps, Grundlehren 299, Springer 1992, https://doi.org/10.1007/978-3-662-02770-7, Chapter 2, Theorem 2.1 (continuous extension iff the boundary is locally connected) with Torhorst's theorem; exterior form via inversion

import Mathlib

theorem ConformalBoundary.caratheodory_torhorst_exterior (γ : unitInterval → ℂ)
    (continuous : Continuous γ) (nondegenerate : ∃ a b, γ a ≠ γ b) :
    ∃ Φ : ℂ → ℂ,
      ContinuousOn Φ {w | 1 ≤ ‖w‖} ∧
      DifferentiableOn ℂ Φ {w | 1 < ‖w‖} ∧
      Set.InjOn Φ {w | 1 < ‖w‖} ∧
      Φ '' {w | 1 < ‖w‖} = {z | z ∉ Set.range γ ∧
        ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)} ∧
      Φ '' Metric.sphere 0 1 = frontier {z | z ∉ Set.range γ ∧
        ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)} ∧
      ∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β,
        Φ (Complex.exp (θ * Complex.I)) ≠ Φ (Complex.exp (α * Complex.I)) := by sorry
