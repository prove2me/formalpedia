-- Prove2me | Theorems.Thm_ConvexSDDP_Det_lemma_5_1
-- name    : ConvexSDDP.Det.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:42.754071+00:00
-- url     : https://prove2.me/theorems/a2385722-411c-4151-a2c6-24915b62dc60
-- title:
--   Lemma 5.1, p. 24 — the marginal function of a jointly convex function over a convex multifunction is convex, and attained
-- statement:
--   Let $J:\mathbb R^d\times\mathbb R^p\to\mathbb R\cup\{+\infty\}$ be convex (jointly in $(x,u)$, with convex epigraph) and let $\mathcal U:\mathbb R^d\rightrightarrows\mathbb R^p$ be a convex multifunction. Then the marginal function
--   $$\phi(x)=\inf_{u\in\mathcal U(x)}J(x,u)$$
--   is convex. Moreover, if $J(x,\cdot)$ is lower semicontinuous for every $x$ and every $\mathcal U(x)$ is compact and nonempty, then for every $x$ the infimum is attained: there is $u\in\mathcal U(x)$ with $J(x,u)=\phi(x)$.
--
--   This is the tool behind the convexity of the Bellman functions $V_t$ (Lemma 2.2 (i)) and of the stage values $\hat V^k_t$ (p. 8).
--
--   **Formalization Note** The page prints $J(u)$; its proof ("the marginal function of a jointly convex function") and its use in Lemma 2.2 (i), with $J(x,u)=C_t(x,u)+V_{t+1}(f_t(x,u))$, need the joint form stated here, which contains the printed one. The infimum is an `EReal` infimum ($+\infty$ when $\mathcal U(x)=\emptyset$, possibly $-\infty$). The attainment part is stated under the same convexity hypotheses, as on the page ("Moreover").
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 24, Lemma 5.1

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic

namespace ConvexSDDP.Det

theorem lemma_5_1 {d p : ℕ}
    (J : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin p) → EReal)
    (hJbot : ∀ x u, J x u ≠ ⊥)
    (hJ : EConvex (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => J z.1 z.2))
    (U : EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin p)))
    (hU : ConvexMultifunction U) :
    EConvex (fun x => ⨅ u ∈ U x, J x u) ∧
      ((∀ x, LowerSemicontinuous (J x)) → (∀ x, IsCompact (U x) ∧ (U x).Nonempty) →
        ∀ x, ∃ u ∈ U x, J x u = ⨅ v ∈ U x, J x v) := by sorry

end ConvexSDDP.Det
