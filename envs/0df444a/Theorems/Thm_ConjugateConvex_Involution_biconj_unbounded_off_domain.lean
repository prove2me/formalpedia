-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_biconj_unbounded_off_domain
-- name    : ConjugateConvex.Involution.biconj_unbounded_off_domain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:46:56.589984+00:00
-- url     : https://prove2.me/theorems/11ec23c2-21ed-4f6c-90a7-527d5cc743f5
-- title:
--   (7), §4, pp. 76–77 — l.u.b. over ξ in Γ of (Σξx° − φ(ξ)) = ∞ for x° not in G
-- statement:
--   Let $(G, f)$ belong to the standing class: $G \subseteq \mathbb R^n$ nonempty and convex, $f$ convex and semi-continuous from below on $G$, and $f(x) \to +\infty$ as $x$ approaches, within $G$, any boundary point of $G$ not in $G$. Let $(\Gamma, \varphi)$ be its conjugate pair. Then for every point $x^\circ \in \mathbb R^n$ not in $G$,
--
--   $$
--   \sup_{\xi \in \Gamma}\bigl(\Sigma\xi x^\circ - \varphi(\xi)\bigr) = \infty, \tag{7}
--   $$
--
--   that is, the function $\xi \mapsto \Sigma\xi x^\circ - \varphi(\xi)$ is unbounded above on $\Gamma$, so $x^\circ$ does not belong to $G^*$.
--
--   With (6) this gives $G^* = G$. The condition that $G$ be closed relative to $f$ is essential here: for $G = (0, 1]$ and $f \equiv 0$ the point $x^\circ = 0$ would lie in $G^*$.
--
--   **Formalization Note** "$= \infty$" is stated as `¬ BddAbove` of the image of $\Gamma$ under $\xi \mapsto \Sigma\xi x^\circ - \varphi(\xi)$, which is exactly $x^\circ \notin G^*$. The term $\Sigma\xi x^\circ$ is `ξ ⬝ᵥ x₀`, as on the page.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), pp. 76–77, §4, (7)

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun
import Definitions.Def_ConjugateConvex_Involution_IsClosedConvexPair

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §4, pp. 76–77, (7): for `x° ∉ G`, `l.u.b._{ξ∈Γ} (Σξx° − φ(ξ)) = ∞`, i.e. the
function `ξ ↦ Σξx° − φ(ξ)` is unbounded above on `Γ`, so `x° ∉ G*`. -/
theorem biconj_unbounded_off_domain {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) :
    ∀ x₀ ∉ G,
      ¬ BddAbove ((fun ξ => ξ ⬝ᵥ x₀ - conjFun G f ξ) '' conjDomain G f) := by sorry

end ConjugateConvex.Involution
