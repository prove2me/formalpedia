-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_cta_solvable_of_insolvable
-- name    : FirstOrderOpt.ConvexTheory.cta_solvable_of_insolvable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T17:36:03.413353+00:00
-- url     : https://prove2.me/theorems/de082610-9a66-49bd-8064-d1b0c6a2cb0a
-- title:
--   Proposition 2.9 — Convex Theorem on Alternative, solvable direction
-- statement:
--   Fix a nonempty convex set $X$, convex functions $f, g_1,\dots,g_m : X \to \mathbb{R}$, and a
--   real number $c$. Consider system (I) on $x$:
--   $$f(x) < c, \quad g_j(x) \le 0\ (j=1,\dots,m), \quad x \in X,$$
--   and system (II) on $\lambda$:
--   $$\inf_{x \in X}\Big[f(x) + \sum_{j=1}^m \lambda_j g_j(x)\Big] \ge c, \quad \lambda_j \ge 0\
--   (j=1,\dots,m).$$
--   **Proposition 2.9.** If (I) is insolvable and the Slater subsystem $g_j(x) < 0$
--   $(j=1,\dots,m)$, $x \in X$ is solvable, then (II) is solvable.
--
--   This is the nontrivial half of the Convex Theorem on Alternative: the trivial half
--   (solvability of (II) implies insolvability of (I)) is Proposition 2.8, immediate from the
--   definitions. Proposition 2.9 is what feeds directly into the proof of strong duality
--   (Theorem 2.6): applied with $c = f^*$ and $f^* - \varepsilon$, it produces a multiplier
--   $\lambda^*$ certifying that the Lagrange dual value matches the primal optimum.
--
--   **Formalization Note.** "$\inf_{x\in X}[\cdots] \ge c$" is stated in the equivalent
--   pointwise form $\forall x \in X, c \le f(x) + \sum_j \lambda_j g_j(x)$, which avoids
--   committing to a particular `sInf` convention and is definitionally what "$c$ is a lower
--   bound of the infimum" means. Convexity of $X$, $f$ and each $g_j$ is the standing
--   hypothesis of §2.3 under which the proof (separating $S$ from $T$ via Theorem 2.1) runs,
--   even though Proposition 2.9's own statement does not repeat it.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 39, Proposition 2.9

import Mathlib

namespace FirstOrderOpt.ConvexTheory

/-- Proposition 2.9 (the nontrivial half of the Convex Theorem on Alternative). System (I) is
`f(x) < c, g_j(x) ≤ 0 (j = 1,…,m), x ∈ X`; its insolvability, together with the Slater
subsystem `g_j(x) < 0 (j = 1,…,m), x ∈ X` being solvable, forces system (II) —
`inf_{x∈X}[f(x) + Σⱼ λⱼ gⱼ(x)] ≥ c, λ ≥ 0` — to be solvable. `X` convex and `f, g` convex on `X`
are the standing hypotheses of §2.3 under which the proof (via separating `S` from `T`) runs. -/
theorem cta_solvable_of_insolvable {n m : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : ℝ) (hXconv : Convex ℝ X) (hfconv : ConvexOn ℝ X f) (hgconv : ∀ j, ConvexOn ℝ X (g j))
    (hI : ¬ ∃ x ∈ X, f x < c ∧ ∀ j, g j x ≤ 0)
    (hSlaterSub : ∃ x ∈ X, ∀ j, g j x < 0) :
    ∃ lam : Fin m → ℝ, (∀ j, 0 ≤ lam j) ∧ ∀ x ∈ X, c ≤ f x + ∑ j, lam j * g j x := by sorry

end FirstOrderOpt.ConvexTheory
