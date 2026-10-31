-- Prove2me | Theorems.Thm_AdaOGD_nash_exists_unique
-- name    : AdaOGD.nash_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:23.859613+00:00
-- url     : https://prove2.me/theorems/95125416-d2e2-445d-821f-9120ab70d038
-- title:
--   §3.1, p.14 — every strongly monotone game has a unique Nash equilibrium
-- statement:
--   Let $\mathcal G$ be a continuous game with nonempty convex compact action sets $\mathcal X_i$, and suppose $\mathcal G$ is $\beta$-strongly monotone with $\beta>0$. Then $\mathcal G$ has exactly one Nash equilibrium $x^\star\in\mathcal X$.
--
--   The paper attributes existence to Debreu (1952) for convex action sets and individually convex costs, and uniqueness to Zhou et al. (2021). This is the clause "where $x^\star\in\mathcal X$ is the unique Nash equilibrium" of Lemma 3.10 and Theorem 3.7.
--
--   Differences from the source:
--   - reading: Definition 3.1, p.13: each $\mathcal X_i$ convex and bounded → each $\mathcal X_i$ also compact (`IsCompact (G.X i)`); reason: p.1 fixes the action set as convex and compact; closedness is needed for the argmin of Algorithm 3 and for the Nash equilibrium to exist (on $\mathcal X=(0,1)$, $u(x)=(x+1)^2/2$ is $1$-strongly monotone and has no equilibrium)
--   - encoding: $u_i$ continuously differentiable in $x_i$ with $v_i=\nabla_{x_i}u_i$ (Definition 3.1) → $v_i(x)$ is a gradient of $x_i\mapsto u_i(x_i;x_{-i})$ within $\mathcal X_i$ (`HasGradientWithinAt`), $v$ continuous on $\mathcal X$; each $\mathcal X_i$ nonempty; reason: costs are defined on $\mathcal X$ only, so the derivative is taken within $\mathcal X_i$; nonempty action sets are the standing convention (Algorithm 3 starts from $x_i^1\in\mathcal X_i$)
--   - encoding: agents $\mathcal N=\{1,\dots,N\}$, $x\in\prod_i\mathbb R^{d_i}$ with the Euclidean norm, $\beta$-strongly monotone → agents `Fin N` ($N=0$ is the trivial game), joint space `PiLp 2` ($\|x\|^2=\sum_i\|x_i\|^2$), $\beta>0$; reason: Lean conventions; the same instances
-- source:
--   Jordan, Lin & Zhou, Adaptive, Doubly Optimal No-Regret Learning in Strongly Monotone and Exp-Concave Games with Gradient Feedback, arXiv:2310.14085v4, §3.1, p.14, "every strongly monotone game admits a unique Nash equilibrium [Zhou et al., 2021]"; existence: "Debreu [1952] proved that any continuous game admits at least one Nash equilibrium …"

import Mathlib
import Definitions.Def_AdaOGD_ContinuousGame

namespace AdaOGD

/-- Every strongly monotone game admits a unique Nash equilibrium (Jordan, Lin & Zhou,
arXiv:2310.14085v4, §3.1, p.14, "every strongly monotone game admits a unique Nash equilibrium
[Zhou et al., 2021]"; existence via "Debreu [1952] proved that any continuous game admits at least
one Nash equilibrium …").

**Formalization Note** The action sets are compact (the paper's p.1, "X ⊆ ℝᵈ is a convex and
compact set"); nonemptiness and convexity are part of `ContinuousGame`. `β > 0`. -/
theorem nash_exists_unique {N : ℕ} {d : Fin N → ℕ} (G : ContinuousGame d)
    (hcompact : ∀ i, IsCompact (G.X i)) {β : ℝ} (hβ : 0 < β) (hmono : IsStronglyMonotone G β) :
    ∃! xs : Joint d, IsNash G xs := by sorry

end AdaOGD
