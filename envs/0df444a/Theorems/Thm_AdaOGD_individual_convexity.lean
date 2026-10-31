-- Prove2me | Theorems.Thm_AdaOGD_individual_convexity
-- name    : AdaOGD.individual_convexity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:09.747737+00:00
-- url     : https://prove2.me/theorems/b6023bed-5fa3-4f20-8413-cfb43a5b964e
-- title:
--   §3.1, p.14 — strongly monotone games are individually convex
-- statement:
--   Let $\mathcal G$ be a continuous game that is $\beta$-strongly monotone with $\beta>0$. Then for every agent $i$ and every joint action $x\in\mathcal X$, the cost
--   $$
--   y\ \longmapsto\ u_i(y;x_{-i})
--   $$
--   is convex on $\mathcal X_i$.
--
--   This is the "individual convexity condition" under which Proposition 3.4 characterizes Nash equilibria by a variational inequality, and under which equilibria exist.
--
--   Differences from the source:
--   - encoding: $u_i$ continuously differentiable in $x_i$ with $v_i=\nabla_{x_i}u_i$ (Definition 3.1) → $v_i(x)$ is a gradient of $x_i\mapsto u_i(x_i;x_{-i})$ within $\mathcal X_i$ (`HasGradientWithinAt`), $v$ continuous on $\mathcal X$; each $\mathcal X_i$ nonempty; reason: costs are defined on $\mathcal X$ only, so the derivative is taken within $\mathcal X_i$; nonempty action sets are the standing convention (Algorithm 3 starts from $x_i^1\in\mathcal X_i$)
--   - encoding: agents $\mathcal N=\{1,\dots,N\}$, $x\in\prod_i\mathbb R^{d_i}$ with the Euclidean norm, $\beta$-strongly monotone → agents `Fin N` ($N=0$ is the trivial game), joint space `PiLp 2` ($\|x\|^2=\sum_i\|x_i\|^2$), $\beta>0$; reason: Lean conventions; the same instances
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, §3.1, p.14, "Strongly monotone games satisfy the individual convexity condition"

import Mathlib
import Definitions.Def_AdaOGD_ContinuousGame

namespace AdaOGD

/-- Strongly monotone games satisfy the individual convexity condition (Jordan, Lin & Zhou,
Adaptive, Doubly Optimal No-Regret Learning…, arXiv:2310.14085v4, §3.1, p.14, "Strongly monotone
games satisfy the individual convexity condition"): in a `β`-strongly monotone continuous game with
`β > 0`, every cost `xᵢ ↦ uᵢ(xᵢ; x₋ᵢ)` is convex on `𝒳ᵢ` for every fixed `x₋ᵢ` coming from `x ∈ 𝒳`. -/
theorem individual_convexity {N : ℕ} {d : Fin N → ℕ} (G : ContinuousGame d) {β : ℝ}
    (hβ : 0 < β) (hmono : IsStronglyMonotone G β) :
    ∀ i : Fin N, ∀ x ∈ jointSet G.X, ConvexOn ℝ (G.X i) (fun y => G.u i (update x i y)) := by sorry

end AdaOGD
