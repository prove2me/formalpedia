-- Prove2me | Theorems.Thm_DelaunayStretch_lemma_4_9_sliding_gate
-- name    : DelaunayStretch.lemma_4_9_sliding_gate
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:57:58.848165+00:00
-- url     : https://prove2.me/theorems/7b7f3b23-663e-4973-ab16-05e70c751bca
-- title:
--   Lemma 4.9 — sliding the gate along the current circle: $\Delta\mu-U\Delta x+W_{H,U}(\tilde s)-W_{H,U}(s)\le0$
-- statement:
--   Let $U\in\mathbb R$ and let $H$ satisfy (H0), (H1) and (H2). Let $s=(O,G,\delta)$ be a gate state, $O'$ a next disk for $s$, $G'=[a',b']$ the common chord of $\partial O$ and $\partial O'$, and $\delta'$, $\Delta\mu$, $\Delta x$ the new difference, the cost and the progress of the step from $s$ to $O'$. Then $\tilde s=(O,G',\delta')$ is a gate state, and
--
--   $$
--   \Delta\mu-U\,\Delta x+W_{H,U}(\tilde s)-W_{H,U}(s)\le0 .
--   $$
--
--   This pays for the first stage of a step in the proof of Theorem 4.7.
--
--   **Formalization Note** "Satisfies (H0), (H1) and (H2)" is: for some piecewise $C^1$ structure, (H0) and (H1) hold and (H2) holds with respect to it.
--
--   Differences from the source:
--   - encoding: points of ℝ² with coordinates x(z), y(z) and Euclidean norm → points of ℂ with x = re, y = im and ‖z − w‖ = dist z w; reason: ℂ is ℝ² with the Euclidean norm; same instances
--   - encoding: H a real function on Ω × ℝ → H : ℝ⁴ → ℝ, z = (γ, φ, θ, ψ); every hypothesis and conclusion reads H only on Ω × ℝ (on Σ for gate states); reason: Ω × ℝ is open in ℝ⁴, so values and derivatives of H there do not depend on the values outside; same functions
-- source:
--   Mo, Cheng, Ding, The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined, preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026, sha256 49ad9397…f824), Lemma 4.9, p.28

import Mathlib
import Definitions.Def_DelaunayStretch_IsNextDisk
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

namespace DelaunayStretch

/-- **Lemma 4.9 (Sliding the gate along the current circle)** (p.28). Let `U ∈ ℝ`, and let `H`
satisfy (H0), (H1) and (H2). Let `s = (O, G, δ)` be a gate state, let `O′` be a next disk for
`s`, let `G′ = [a′, b′]` be the common chord of `∂O` and `∂O′`, and let `δ′`, `Δµ` and `Δx` be
the new difference, the cost and the progress of the step from `s` to `O′`. Then
`s̃ = (O, G′, δ′)` is a gate state, and `Δµ − U Δx + W_{H,U}(s̃) − W_{H,U}(s) ≤ 0` (4.6).

Mo, Cheng, Ding, *The Stretch Factor of Planar Delaunay Triangulations Is Nearly Determined*,
preprint (arXiv:2609.07979, version not stamped; held file of November 3, 2026), Lemma 4.9, p.28.

**Formalization Note** "Satisfies (H0), (H1) and (H2)" is: for some piecewise `C¹` structure
`P` of `H`, (H0), (H1) and (H2) hold, (H2) with respect to `P` (Definition 4.6). -/
theorem lemma_4_9_sliding_gate (U : ℝ) (H : R4 → ℝ)
    (hH : ∃ P : PiecewiseC1 H, CondH0 H ∧ CondH1 H ∧ CondH2 P)
    (s : GateState) (hs : s.IsGateState) (O' : Disk) (a' b' : ℂ) (hO' : IsNextDisk s O' a' b') :
    (⟨s.O, a', b', stepDiff s a' b'⟩ : GateState).IsGateState ∧
    stepCost s a' b' - U * stepProgress s a' b' +
        potential H U ⟨s.O, a', b', stepDiff s a' b'⟩ - potential H U s ≤ 0 := by sorry

end DelaunayStretch
