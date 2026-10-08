-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_conjFun_convexOn
-- name    : ConjugateConvex.Involution.conjFun_convexOn
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:46:15.080986+00:00
-- url     : https://prove2.me/theorems/afbb8d07-f5f0-4e1c-8046-a9238f4c9073
-- title:
--   §3, p. 76 — Γ and φ(ξ) are convex
-- statement:
--   Let $G \subseteq \mathbb R^n$, let $f$ be a real function defined in $G$, and let $(\Gamma, \varphi)$ be its conjugate pair. Then $\Gamma$ is a convex set and $\varphi$ is convex on $\Gamma$: for $\xi', \xi'' \in \Gamma$ and $0 \le \theta \le 1$, the point $(1-\theta)\xi' + \theta\xi''$ lies in $\Gamma$ and
--
--   $$
--   \varphi\bigl((1-\theta)\xi' + \theta\xi''\bigr) \le (1-\theta)\varphi(\xi') + \theta\varphi(\xi'').
--   $$
--
--   This is the first of the properties needed to show that the conjugate pair belongs to the same class as $(G, f)$.
--
--   **Formalization Note** No hypothesis on $(G, f)$ is assumed; the statement holds for every $G$ and $f$ (for $G = \emptyset$, $\Gamma$ is all of $\mathbb R^n$ and $\varphi \equiv 0$ by the convention of the real supremum), which is stronger than the paper's setting. Convexity on $\Gamma$ is Mathlib's `ConvexOn ℝ Γ φ`, which includes convexity of $\Gamma$.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 76, §3 ('It is evident that Γ and φ(ξ) are convex')

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 76: `Γ` and `φ(ξ)` are convex. -/
theorem conjFun_convexOn {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    ConvexOn ℝ (conjDomain G f) (conjFun G f) := by sorry

end ConjugateConvex.Involution
