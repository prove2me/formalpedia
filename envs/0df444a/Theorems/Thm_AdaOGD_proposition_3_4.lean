-- Prove2me | Theorems.Thm_AdaOGD_proposition_3_4
-- name    : AdaOGD.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:07.830689+00:00
-- url     : https://prove2.me/theorems/dc31e351-fa7e-4694-948b-63bd7137d878
-- title:
--   Proposition 3.4 — Nash equilibria of individually convex games are the solutions of the variational inequality
-- statement:
--   Let $\mathcal G$ be a continuous game whose costs are **individually convex**: $y\mapsto u_i(y;x_{-i})$ is convex on $\mathcal X_i$ for every agent $i$ and every $x\in\mathcal X$. Then a joint action $x^\star\in\mathcal X$ is a Nash equilibrium if and only if
--   $$
--   (x-x^\star)^\top v(x^\star)\ \ge\ 0\qquad\text{for all }x\in\mathcal X .
--   $$
--
--   This variational characterization is what the convergence analysis uses at $x^\star$: combined with strong monotonicity it gives $(x^\star-x)^\top v(x)\le-\beta\|x^\star-x\|^2$.
--
--   **Formalization Note** $(x-x^\star)^\top v(x^\star)$ is the inner product of the joint space, $\sum_i\langle x_i-x_i^\star,v_i(x^\star)\rangle$.
--
--   Differences from the source:
--   - encoding: $u_i$ continuously differentiable in $x_i$ with $v_i=\nabla_{x_i}u_i$ (Definition 3.1) → $v_i(x)$ is a gradient of $x_i\mapsto u_i(x_i;x_{-i})$ within $\mathcal X_i$ (`HasGradientWithinAt`), $v$ continuous on $\mathcal X$; each $\mathcal X_i$ nonempty; reason: costs are defined on $\mathcal X$ only, so the derivative is taken within $\mathcal X_i$; nonempty action sets are the standing convention (Algorithm 3 starts from $x_i^1\in\mathcal X_i$)
--   - encoding: agents $\mathcal N$, Euclidean joint space → agents `Fin N`, joint space `PiLp 2`; reason: Lean conventions; the same instances
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, §3.1, Proposition 3.4, p.14 (cited from Facchinei and Pang, 2007)

import Mathlib
import Definitions.Def_AdaOGD_ContinuousGame

namespace AdaOGD

open scoped InnerProductSpace

/-- Proposition 3.4 (Jordan, Lin & Zhou, arXiv:2310.14085v4, p.14; cited from Facchinei and Pang,
2007): if every cost function of a continuous game is individually convex, then a joint action
`x⋆ ∈ 𝒳` is a Nash equilibrium if and only if `(x − x⋆)ᵀ v(x⋆) ≥ 0` for all `x ∈ 𝒳`.

**Formalization Note** Individual convexity is convexity of `xᵢ ↦ uᵢ(xᵢ; x₋ᵢ)` on `𝒳ᵢ` for every
`x ∈ 𝒳` (p.14, "uᵢ(xᵢ; x₋ᵢ) is convex in xᵢ for a fixed x₋ᵢ"). `(x − x⋆)ᵀ v(x⋆)` is the inner
product of the joint space, `∑ᵢ ⟨xᵢ − x⋆ᵢ, vᵢ(x⋆)⟩`. -/
theorem proposition_3_4 {N : ℕ} {d : Fin N → ℕ} (G : ContinuousGame d)
    (hconv : ∀ i : Fin N, ∀ x ∈ jointSet G.X, ConvexOn ℝ (G.X i) (fun y => G.u i (update x i y)))
    (xs : Joint d) (hxs : xs ∈ jointSet G.X) :
    IsNash G xs ↔ ∀ x ∈ jointSet G.X, 0 ≤ ⟪x - xs, G.v xs⟫_ℝ := by sorry

end AdaOGD
