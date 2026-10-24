-- Prove2me | Theorems.Thm_FanGlicksberg_kakutani_fan_glicksberg
-- name    : FanGlicksberg.kakutani_fan_glicksberg
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T06:25:57.551973+00:00
-- url     : https://prove2.me/theorems/f8a6d7a1-43b2-4097-9986-d6814248e717
-- title:
--   Kakutani–Fan–Glicksberg fixed point theorem (upper hemicontinuous, closed convex values)
-- statement:
--   **Kakutani–Fan–Glicksberg fixed point theorem.** Let $E$ be a Hausdorff locally convex real topological vector space and let $K\subseteq E$ be a nonempty, compact, convex set. Let $\Phi:E\rightrightarrows E$ be a correspondence which, on $K$, is upper hemicontinuous and has nonempty, convex, closed values contained in $K$:
--
--   $$\Phi(x)\subseteq K,\qquad \Phi(x)\neq\emptyset,\qquad \Phi(x)\ \text{convex and closed}\qquad (x\in K).$$
--
--   Then $\Phi$ has a fixed point in $K$: there is $x\in K$ with $x\in\Phi(x)$.
--
--   Upper hemicontinuity on $K$ means: for every $x\in K$ and every neighbourhood $V$ of the set $\Phi(x)$, the set $V$ is a neighbourhood of $\Phi(x')$ for all $x'\in K$ close enough to $x$ (Mathlib's `UpperHemicontinuousOn`). An upper hemicontinuous correspondence with closed values into the regular space $E$ has closed graph, so this is the closed-graph form of the theorem (Fan 1952, Glicksberg 1952; Aliprantis–Border, Corollary 17.55). In finite dimensions it is Kakutani's theorem.
--
--   It is the fixed-point theorem applied in the proof of Proposition 2 of Balseiro–Kroer–Kumar (Contextual Standard Auctions with Budgets), to the correspondence $C^*_0$ on the compact convex set $\mathcal X_0\subset L_1(\Theta)$.
-- source:
--   K. Fan, Fixed-point and minimax theorems in locally convex topological linear spaces, PNAS 38 (1952) 121–126, Theorem 1; I. L. Glicksberg, A further generalization of the Kakutani fixed point theorem, Proc. AMS 3 (1952) 170–174, Theorem; Aliprantis & Border, Infinite Dimensional Analysis (3rd ed., 2006), Corollary 17.55 with Theorem 17.10. Used in Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets, Management Science (2023), proof of Proposition 2 (via Lemma 4).

import Mathlib

namespace FanGlicksberg

theorem kakutani_fan_glicksberg {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
    (K : Set E) (hKne : K.Nonempty) (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (Φ : E → Set E) (hΦ : UpperHemicontinuousOn Φ K)
    (hΦK : ∀ x ∈ K, Φ x ⊆ K) (hΦne : ∀ x ∈ K, (Φ x).Nonempty)
    (hΦconv : ∀ x ∈ K, Convex ℝ (Φ x)) (hΦclosed : ∀ x ∈ K, IsClosed (Φ x)) :
    ∃ x ∈ K, x ∈ Φ x := by sorry

end FanGlicksberg
