-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hofer_lemma
-- name    : FiniteEnergyPlane.hofer_lemma
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-20T23:23:42.10926+00:00
-- url     : https://prove2.me/theorems/c225cde5-1c7e-4558-95e3-cdb262c49909
-- title:
--   Hofer's topological lemma
-- statement:
--   Let $(X,d)$ be a complete metric space, $g:X\to[0,\infty)$ continuous, $x_0\in X$ and $\varepsilon_0>0$. Then there are $x\in X$ and $0<\varepsilon\le\varepsilon_0$ such that
--   $$\varepsilon\,g(x)\ge\varepsilon_0\,g(x_0),\qquad d(x,x_0)\le2\varepsilon_0,\qquad g(y)\le2g(x)\ \text{ whenever } d(y,x)\le\varepsilon.$$
--
--   **Formalization Note** Wendl states the last property for $y$ in the open ball $B_\varepsilon(x)$; here it is required on the closed ball `closedBall x ε`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lemma 9.4, p. 154; H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Lemma 26, p. 535

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer's topological lemma: Wendl, Lemma 9.4 (p. 154); Hofer 1993, Lemma 26 (p. 535). Let
`X` be a complete metric space, `g : X → [0, ∞)` continuous, `x₀ ∈ X` and `ε₀ > 0`. There are
`x ∈ X` and `0 < ε ≤ ε₀` with `ε g(x) ≥ ε₀ g(x₀)`, `d(x, x₀) ≤ 2ε₀`, and `g(y) ≤ 2 g(x)` whenever
`d(y, x) ≤ ε`. (Wendl states the last property on the ball `B_ε(x)`; the closed ball is used
here.) -/
theorem hofer_lemma {X : Type*} [MetricSpace X] [CompleteSpace X] (g : X → ℝ)
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (x₀ : X) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ x : X, ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε₀ * g x₀ ≤ ε * g x ∧ dist x x₀ ≤ 2 * ε₀ ∧
      ∀ y ∈ closedBall x ε, g y ≤ 2 * g x := by
  sorry

end FiniteEnergyPlane
