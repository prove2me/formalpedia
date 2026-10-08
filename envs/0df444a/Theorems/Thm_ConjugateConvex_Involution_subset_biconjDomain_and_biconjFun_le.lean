-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_subset_biconjDomain_and_biconjFun_le
-- name    : ConjugateConvex.Involution.subset_biconjDomain_and_biconjFun_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:46:28.133978+00:00
-- url     : https://prove2.me/theorems/8f7c63d6-e753-4f53-a299-6ef10d09c5ec
-- title:
--   (6), §4, p. 76 — Σξx − φ(ξ) ≤ f(x), hence G ⊂ G* and f*(x) ≤ f(x) in G
-- statement:
--   Let $G \subseteq \mathbb R^n$, let $f$ be a real function defined in $G$, and let $(\Gamma, \varphi)$ be its conjugate pair. Let $(G^*, f^*)$ be the conjugate pair of $(\Gamma, \varphi)$: $G^*$ is the set of $x$ for which $\Sigma\xi x - \varphi(\xi)$ is bounded from above on $\Gamma$, and $f^*(x) = \sup_{\xi \in \Gamma}(\Sigma\xi x - \varphi(\xi))$. Assume $\Gamma \neq \emptyset$. Then for every $x \in G$, by (5),
--
--   $$
--   \Sigma\xi x - \varphi(\xi) \le f(x) \quad \text{for all } \xi \in \Gamma, \tag{6}
--   $$
--
--   hence $x \in G^*$ and $f^*(x) \le f(x)$. That is, $G \subseteq G^*$ and $f^* \le f$ on $G$.
--
--   This is the easy half of the involution $(G^*, f^*) = (G, f)$.
--
--   **Formalization Note** The pair $(G^*, f^*)$ is the same definition (`conjDomain`, `conjFun`) applied to $(\Gamma, \varphi)$. The only hypothesis is $\Gamma \neq \emptyset$, needed because the real supremum of an empty set is $0$; the standing class implies it (§3, p. 75), so this statement is stronger than the paper's.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 76, §4, (6) and 'hence G ⊂ G* and f*(x) ≦ f(x) in G'

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §4, p. 76, (6): for `x ∈ G`, `Σξx − φ(ξ) ≦ f(x)` for all `ξ ∈ Γ`,
hence `G ⊂ G*` and `f*(x) ≦ f(x)` in `G`. Here `G* = conjDomain Γ φ` and `f* = conjFun Γ φ`. -/
theorem subset_biconjDomain_and_biconjFun_le {n : ℕ} (G : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (hΓ : (conjDomain G f).Nonempty) :
    ∀ x ∈ G, x ∈ conjDomain (conjDomain G f) (conjFun G f) ∧
      conjFun (conjDomain G f) (conjFun G f) x ≤ f x := by sorry

end ConjugateConvex.Involution
