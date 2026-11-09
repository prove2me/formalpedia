-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_4_11_initial_final
-- name    : DelaunayStretch.lemma_4_11_initial_final
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:57:36.950208+00:00
-- url     : https://prove2.me/theorems/fc006393-0004-49c0-a084-092e76dbc6d1
-- title:
--   Lemma 4.11 — initial pairs and final steps satisfy (4.8) and (4.9)
-- statement:
--   Let $U\in\mathbb R$ and let $H$ satisfy (H1) and (H3) at level $U$.
--
--   1. For every initial pair $(O_1,O_2)$, with $G_1=[a_1,b_1]$ the common chord, $c_1$ its crossing with the $x$-axis, $u=w_-(O_1)$, and $\delta_1$, $\mu_1$ the difference and the cost of the initial pair, the triple $\tilde s_1=(O_1,G_1,\delta_1)$ is a gate state and
--   $$
--   \mu_1-U\,(x(c_1)-x(u))+W_{H,U}(\tilde s_1)\le0 .
--   $$
--   2. For every gate state $s=(O,G,\delta)$, the cost $\kappa$ of the final step at $s$ satisfies
--   $$
--   \kappa-U\,(x(w_+(O))-x(c(s)))-W_{H,U}(s)\le0 .
--   $$
--
--   These inequalities pay for the two ends of a chain.
--
--   **Formalization Note** (H1) and (H3) do not refer to a piecewise $C^1$ structure, and none is assumed.
--
--   Differences from the source:
--   - generalization: H satisfies (H1) and (H3) in the sense of Definition 4.6, which also posits a piecewise C¹ structure for H → H satisfies (H1) and (H3); no piecewise C¹ structure is assumed; reason: neither condition refers to the structure, so every H allowed by the source is allowed here
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: H a real function on Ω × ℝ → H : ℝ⁴ → ℝ, z = (γ, φ, θ, ψ); every hypothesis and conclusion reads H only on Ω × ℝ (on Σ for gate states); reason: Ω × ℝ is open in ℝ⁴, so values and derivatives of H there do not depend on the values outside; same functions
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma 4.11, p.29

import Mathlib
import Definitions.Def_DelaunayStretch_IsNextDisk
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Lemma 4.11 (Initial pairs and final steps)** (p.29). Let `U ∈ ℝ`, and let `H` satisfy
(H1) and (H3) at level `U`.

1. For every initial pair `(O₁, O₂)`, with `G₁ = [a₁, b₁]` the common chord of `∂O₁` and
   `∂O₂`, `c₁` its crossing with the `x`-axis, `u = w₋(O₁)`, and `δ₁` and `µ₁` the difference
   and the cost of the initial pair, the triple `s̃₁ = (O₁, G₁, δ₁)` is a gate state, and
   `µ₁ − U(x(c₁) − x(u)) + W_{H,U}(s̃₁) ≤ 0` (4.8).
2. For every gate state `s = (O, G, δ)`, the cost `κ` of the final step at `s` satisfies
   `κ − U(x(w₊(O)) − x(c(s))) − W_{H,U}(s) ≤ 0` (4.9).

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma 4.11, p.29.

**Formalization Note** Only (H1) and (H3) are assumed; neither refers to a piecewise `C¹`
structure, so the existence of one (part of the wording of Definition 4.6) is not assumed. -/
theorem lemma_4_11_initial_final (U : ℝ) (H : R4 → ℝ) (h1 : CondH1 H) (h3 : CondH3 U H) :
    (∀ (O₁ O₂ : Disk) (a₁ b₁ : ℂ), IsInitialPair O₁ O₂ a₁ b₁ →
      (⟨O₁, a₁, b₁, initialDiff O₁ a₁ b₁⟩ : GateState).IsGateState ∧
        initialCost O₁ a₁ b₁ - U * initialProgress O₁ a₁ b₁ +
          potential H U ⟨O₁, a₁, b₁, initialDiff O₁ a₁ b₁⟩ ≤ 0) ∧
    (∀ s : GateState, s.IsGateState →
      finalCost s - U * finalProgress s - potential H U s ≤ 0) := by sorry

end DelaunayStretch
