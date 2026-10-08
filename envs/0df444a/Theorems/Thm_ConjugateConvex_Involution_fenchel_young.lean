-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_fenchel_young
-- name    : ConjugateConvex.Involution.fenchel_young
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:45:51.619072+00:00
-- url     : https://prove2.me/theorems/e6ac8d37-ab4e-4a41-b25b-15afa55f7c94
-- title:
--   (5), §3, p. 75 — Σxξ ≤ f(x) + φ(ξ) for x in G and ξ in Γ
-- statement:
--   Let $G \subseteq \mathbb R^n$, let $f$ be a real function defined in $G$, and let $(\Gamma, \varphi)$ be its conjugate pair: $\Gamma$ is the set of $\xi$ for which $\Sigma x\xi - f(x)$ is bounded above on $G$, and $\varphi(\xi) = \sup_{x \in G}(\Sigma x\xi - f(x))$. Then for every $x \in G$ and every $\xi \in \Gamma$,
--
--   $$
--   \Sigma x\xi \le f(x) + \varphi(\xi). \tag{5}
--   $$
--
--   This is Fenchel's inequality (5), the $n$-dimensional form of Young's inequality. It is the basic estimate of the theorem: every later step of the proof starts from it.
--
--   **Formalization Note** The statement needs none of the hypotheses of the standing class (convexity, semi-continuity, closedness relative to $f$, nonemptiness); it holds for every $G$ and $f$, which is stronger than the paper's setting.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 75, §3, (5) ('Then (5) is valid')

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75, (5): `Σxξ ≦ f(x) + φ(ξ)` for `x ∈ G`, `ξ ∈ Γ`. -/
theorem fenchel_young {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    ∀ x ∈ G, ∀ ξ ∈ conjDomain G f, x ⬝ᵥ ξ ≤ f x + conjFun G f ξ := by sorry

end ConjugateConvex.Involution
