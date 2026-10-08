-- Prove2me | Theorems.Thm_ConjugateConvex_Involution_support_at_intrinsicInterior
-- name    : ConjugateConvex.Involution.support_at_intrinsicInterior
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:45:59.099987+00:00
-- url     : https://prove2.me/theorems/ec463a6a-7638-4564-bdc5-077719daafdc
-- title:
--   §3, p. 75 — Γ is not empty, and φ(ξ) = Σx°ξ − f(x°) for some ξ in Γ at each interior point x° of G
-- statement:
--   Let $G \subseteq \mathbb R^n$ be nonempty and convex, let $f$ be convex on $G$, and let $(\Gamma, \varphi)$ be the conjugate pair of $(G, f)$. Then
--
--   1. $\Gamma$ is not empty;
--   2. for every relative-interior point $x^\circ$ of $G$ there is $\xi \in \Gamma$ with
--   $$
--   \varphi(\xi) = \Sigma x^\circ\xi - f(x^\circ).
--   $$
--
--   Geometrically, the hyperplane $y = \Sigma x\xi - \varphi(\xi)$ in $\mathbb R^{n+1}$ supports the graph of $f$ at $(x^\circ, f(x^\circ))$. Part 2 is exactly the assertion of the theorem that equality in (5) is attained at every interior point of $G$.
--
--   **Formalization Note** "Interior point of $G$" is read as a point of the relative interior of $G$ (Mathlib's `intrinsicInterior ℝ G`, the interior of $G$ within its affine hull). The paper's §2 defines an interior point as an interior point of a segment contained in $G$; under that literal reading the claim is false: for $G = \{x \in \mathbb R^2 : x_1 \ge 0\}$, $f(x) = -\sqrt{x_1}$, the origin is interior to the segment from $(0,-1)$ to $(0,1)$ but no supporting hyperplane passes through $(0, f(0))$. For $n$-dimensional $G$ the relative interior is the ordinary interior. Lower semicontinuity and the blow-up condition are not needed and not assumed.
-- source:
--   Fenchel, On conjugate convex functions, Canad. J. Math. 1 (1949), p. 75, §3 ('This shows that Γ is not empty … this proves the assertion on the equality sign in (5)')

import Mathlib
import Definitions.Def_ConjugateConvex_Involution_conjDomain
import Definitions.Def_ConjugateConvex_Involution_conjFun

namespace ConjugateConvex.Involution

/-- Fenchel (1949), §3, p. 75: `Γ` is not empty, and through every interior point `x°` of `G`
(read as a relative-interior point) there is a hyperplane of support with normal `(ξ, −1)`,
so that `φ(ξ) = Σx°ξ − f(x°)` for some `ξ ∈ Γ`. -/
theorem support_at_intrinsicInterior {n : ℕ} (G : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hG : G.Nonempty) (hf : ConvexOn ℝ G f) :
    (conjDomain G f).Nonempty ∧
      ∀ x₀ ∈ intrinsicInterior ℝ G,
        ∃ ξ ∈ conjDomain G f, conjFun G f ξ = x₀ ⬝ᵥ ξ - f x₀ := by sorry

end ConjugateConvex.Involution
