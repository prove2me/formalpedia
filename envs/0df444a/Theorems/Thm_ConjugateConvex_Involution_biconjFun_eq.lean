-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_biconjFun_eq
-- name    : ConjugateConvex.Involution.biconjFun_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:46:40.233996+00:00
-- url     : https://prove2.me/theorems/ee7cae6f-9d89-4f5f-85bc-13e58090ba6e
-- title:
--   §4, p. 76 — f*(x) = f(x) at every point of G
-- statement:
--   Let $G \subseteq \mathbb R^n$ be nonempty and convex, let $f$ be convex and semi-continuous from below on $G$, let $(\Gamma, \varphi)$ be the conjugate pair of $(G, f)$, and let $f^*(x) = \sup_{\xi \in \Gamma}(\Sigma\xi x - \varphi(\xi))$ be the conjugate function of $(\Gamma, \varphi)$. Then
--
--   $$
--   f^*(x) = f(x) \quad \text{for every } x \in G.
--   $$
--
--   This is the identity of values in the involution: a convex function semi-continuous from below on its domain is the supremum of its affine minorants $x \mapsto \Sigma\xi x - \varphi(\xi)$, $\xi \in \Gamma$.
--
--   **Formalization Note** The condition that $G$ be closed relative to $f$ is not assumed: it is needed for $G^* = G$ (see the milestone for (7)) but not for $f^* = f$ on $G$, so this statement is stronger than the paper's. Nonemptiness of $G$ is the mission's pin; for empty $G$ the real supremum conventions make the statement vacuous anyway.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 76, §4 ('Hence f*(x) = f(x) at the interior points of G and … also at the boundary points of G')

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §4, p. 76: `f*(x) = f(x)` at every point of `G`, where
`f* = conjFun Γ φ` is the conjugate of `(Γ, φ) = (conjDomain G f, conjFun G f)`. -/
theorem biconjFun_eq {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hG : G.Nonempty) (hf : ConvexOn ℝ G f) (hfl : LowerSemicontinuousOn f G) :
    ∀ x ∈ G, conjFun (conjDomain G f) (conjFun G f) x = f x := by sorry

end ConjugateConvex.Involution
