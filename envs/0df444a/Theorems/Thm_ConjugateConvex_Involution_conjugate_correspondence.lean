-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_conjugate_correspondence
-- name    : ConjugateConvex.Involution.conjugate_correspondence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:46:54.432126+00:00
-- url     : https://prove2.me/theorems/1be8aba9-0bda-497a-baf4-2b7d4b36352c
-- title:
--   Theorem, §3, p. 75 — the conjugate (Γ, φ) has the properties of (G, f), satisfies (5) with equality at interior points, and conjugates back to (G, f)
-- statement:
--   Let $G \subseteq \mathbb R^n$ be a nonempty convex set and $f$ a real function defined in $G$, convex and semi-continuous from below on $G$, such that $f(x) \to +\infty$ as $x \to x^*$ within $G$ for each boundary point $x^*$ of $G$ which does not belong to $G$. Let
--
--   $$
--   \Gamma = \{\xi : \Sigma x\xi - f(x) \text{ is bounded above on } G\}, \qquad \varphi(\xi) = \sup_{x \in G}\bigl(\Sigma x\xi - f(x)\bigr) \ (\xi \in \Gamma).
--   $$
--
--   Then:
--
--   1. $(\Gamma, \varphi)$ has exactly the same properties as $(G, f)$: $\Gamma$ is nonempty and convex, $\varphi$ is convex and semi-continuous from below on $\Gamma$, and $\varphi(\xi) \to +\infty$ at every boundary point of $\Gamma$ not in $\Gamma$;
--   2. for all $x \in G$ and $\xi \in \Gamma$,
--   $$
--   \Sigma x\xi \le f(x) + \varphi(\xi); \tag{5}
--   $$
--   3. to every relative-interior point $x$ of $G$ there corresponds at least one $\xi \in \Gamma$ for which equality holds in (5);
--   4. in the same way $(G, f)$ corresponds to $(\Gamma, \varphi)$: the set of $x$ for which $\Sigma\xi x - \varphi(\xi)$ is bounded above on $\Gamma$ is exactly $G$, and $\sup_{\xi \in \Gamma}(\Sigma\xi x - \varphi(\xi)) = f(x)$ for every $x \in G$;
--   5. $(\Gamma, \varphi)$ is the only pair with this symmetry: if $(\Gamma', \varphi')$ has the properties in 1 and its conjugate pair is $(G, f)$ (domain exactly $G$, values $f$ on $G$), then $\Gamma' = \Gamma$ and $\varphi' = \varphi$ on $\Gamma'$.
--
--   This is Fenchel's theorem: conjugation is a symmetric, one-to-one correspondence on the class of convex functions that are semi-continuous from below on a convex domain closed relative to the function. It is the origin of the Legendre–Fenchel transform in $\mathbb R^n$ and of the biconjugation theorem $f^{**} = f$.
--
--   **Formalization Note** Three readings are fixed. (P1) $G$ is assumed nonempty; the paper's "convex region" is tacitly nonempty, and the paper proves $\Gamma \neq \emptyset$, so nonemptiness is one of "the same properties". (P2) "Interior point of $G$" is read as relative-interior point (`intrinsicInterior ℝ G`); the paper's literal segment definition makes part 3 false ($G = \{x_1 \ge 0\} \subset \mathbb R^2$, $f = -\sqrt{x_1}$, $x = 0$), while for $n$-dimensional $G$ the two notions of interior agree with the topological one. (P3) The paper's "one and only one $\Gamma$ … and one and only one $\varphi$ … with exactly the same properties … such that (5) … equality" is false as literally read: for $G = [0,1]$, $f \equiv 0$ the conjugate is $\Gamma = \mathbb R$, $\varphi(\xi) = \max(0, \xi)$, yet $\Gamma' = \{0\}$, $\varphi'(0) = 0$ also has every listed property, satisfies (5) and attains equality at every $x \in (0,1)$. The paper never argues uniqueness separately; its proof establishes the symmetry 4, from which the uniqueness 5 follows, and 5 is what is stated. Points are `Fin n → ℝ` and $\Sigma x\xi$ is `x ⬝ᵥ ξ`; the second conjugate is the same definition (`conjDomain`, `conjFun`) applied to $(\Gamma, \varphi)$, whose summand `ξ ⬝ᵥ x` is the paper's $\Sigma\xi x$. The real supremum $\varphi$ is evaluated only on $\Gamma$.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 75, Theorem (§3) and (5); proof in §3–§4, pp. 75–77

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun
import Definitions.Def_ConjugateConvex_Involution_IsClosedConvexPair

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75, the Theorem, with (5); proved in §§3–4, pp. 75–77.
For `(G, f)` in the standing class, the conjugate `(Γ, φ)` is again in the class, satisfies (5)
with equality attained at every (relative) interior point of `G`, and conjugates back to `(G, f)`
(`G* = G`, `f* = f` on `G`). Uniqueness is stated in the form the proof gives: any pair `(Γ′, φ′)`
in the class whose conjugate is `(G, f)` is `(Γ, φ)`. -/
theorem conjugate_correspondence {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hGf : IsClosedConvexPair G f) :
    IsClosedConvexPair (conjDomain G f) (conjFun G f) ∧
    (∀ x ∈ G, ∀ ξ ∈ conjDomain G f, x ⬝ᵥ ξ ≤ f x + conjFun G f ξ) ∧
    (∀ x ∈ intrinsicInterior ℝ G, ∃ ξ ∈ conjDomain G f, x ⬝ᵥ ξ = f x + conjFun G f ξ) ∧
    conjDomain (conjDomain G f) (conjFun G f) = G ∧
    (∀ x ∈ G, conjFun (conjDomain G f) (conjFun G f) x = f x) ∧
    (∀ (Γ' : Set (Fin n → ℝ)) (φ' : (Fin n → ℝ) → ℝ), IsClosedConvexPair Γ' φ' →
      conjDomain Γ' φ' = G → (∀ x ∈ G, conjFun Γ' φ' x = f x) →
      Γ' = conjDomain G f ∧ ∀ ξ ∈ Γ', φ' ξ = conjFun G f ξ) := by sorry

end ConjugateConvex.Involution
