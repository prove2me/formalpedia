-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorProx_theorem_4_4
-- name    : ConvexOptAlg.MirrorProx.theorem_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:23:34.66801+00:00
-- url     : https://prove2.me/theorems/93cf2234-7e62-402b-b143-df0ea72c5c64
-- title:
--   Theorem 4.4, p. 305 — mirror prox with η = ρ/β on a convex β-smooth f satisfies f((1/t)Σ_{s=1}^t y_{s+1}) − f(x*) ≤ βR²/(ρt)
-- statement:
--   Fix an arbitrary norm $\|\cdot\|$ on a finite-dimensional real space, a compact convex set $\mathcal X$, and a convex open set $\mathcal D$ with $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\ne\emptyset$. Let $\Phi$ be a mirror map on $\mathcal D$ that is $\rho$-strongly convex on $\mathcal X\cap\mathcal D$ with respect to $\|\cdot\|$, with $\rho>0$. Let $f$ be convex and $\beta$-smooth on $\mathcal X$ with respect to $\|\cdot\|$, with $\beta>0$, and let $x^*\in\mathcal X$ minimize $f$ over $\mathcal X$. Run mirror prox with $\eta=\rho/\beta$ from $x_1\in\operatorname{argmin}_{x\in\mathcal X\cap\mathcal D}\Phi(x)$, and let $R$ satisfy
--   $$\Phi(x)-\Phi(x_1)\le R^2\qquad\text{for all }x\in\mathcal X\cap\mathcal D,$$
--   for instance $R^2=\sup_{x\in\mathcal X\cap\mathcal D}\Phi(x)-\Phi(x_1)$. Then for every $t\ge1$,
--   $$f\Bigl(\frac1t\sum_{s=1}^t y_{s+1}\Bigr)-f(x^*)\le\frac{\beta R^2}{\rho t}.$$
--
--   Mirror prox, introduced by Nemirovski, attains the rate $1/t$ on smooth functions in non-Euclidean geometries, while mirror descent attains $1/\sqrt t$ on Lipschitz functions (Theorem 4.2). The average is over the intermediate points $y_{s+1}$, not over the $x_s$.
--
--   **Formalization Note** The existence of the minimizer $x^*$ is the book's standing assumption (p. 242). The book does not specify $x_1$ in §4.5; it is taken in $\operatorname{argmin}_{\mathcal X\cap\mathcal D}\Phi$ as in mirror descent (§4.2, p. 299), which is what makes $R^2$ bound $D_\Phi(x,x_1)$. $R$ is any real with $\Phi-\Phi(x_1)\le R^2$ on $\mathcal X\cap\mathcal D$; the book's $R^2=\sup$ is the special case where the supremum is finite (when it is $+\infty$ the book's bound is void). $\rho>0$ and $\beta>0$ are the implicit conditions for $\eta=\rho/\beta$ and the division by $\rho t$. The gradient of $f$ is required relative to $\mathcal X$ (`HasFDerivWithinAt`), matching $f:\mathcal X\to\mathbb R$; $x^*$ may lie on the boundary of $\mathcal D$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Theorem 4.4, p. 305 (mirror prox equations, p. 305; proof, pp. 306–307)

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

namespace ConvexOptAlg.MirrorProx

/-- Theorem 4.4 (Bubeck, arXiv:1405.4980v2, §4.5, p. 305). Fix a norm on a finite-dimensional real
space `E`, a compact convex set `X`, and a convex open set `D` with `X ⊆ closure D` and
`X ∩ D ≠ ∅`. Let `Φ` be a mirror map on `D`, `ρ`-strongly convex on `X ∩ D` w.r.t. `‖·‖`
(`ρ > 0`), and let `f` be convex and `β`-smooth on `X` w.r.t. `‖·‖` (`β > 0`), with a minimizer
`x∗ ∈ X`. Let `(x_t, y_t, y'_t, x'_t)` be a run of mirror prox with `η = ρ/β` started at
`x₁ ∈ argmin_{X ∩ D} Φ`, and let `R` satisfy `Φ(w) − Φ(x₁) ≤ R²` for all `w ∈ X ∩ D` (the
book's `R² = sup_{X ∩ D} Φ − Φ(x₁)` is one such value). Then for every `t ≥ 1`,
`f((1/t) Σ_{s=1}^t y_{s+1}) − f(x∗) ≤ βR²/(ρt)`. -/
theorem theorem_4_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' ρ)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (hf : ConvexOn ℝ X f)
    (β : ℝ) (hβ : 0 < β) (hsm : IsSmoothWRT X f f' β)
    (xstar : E) (hxstar : xstar ∈ X ∧ ∀ w ∈ X, f xstar ≤ f w)
    (x y y' x' : ℕ → E) (hrun : IsMirrorProxRun X D Φ Φ' f' (ρ / β) x y y' x')
    (hx1 : ∀ w ∈ X ∩ D, Φ (x 1) ≤ Φ w)
    (R : ℝ) (hR : ∀ w ∈ X ∩ D, Φ w - Φ (x 1) ≤ R ^ 2)
    (t : ℕ) (ht : 1 ≤ t) :
    f ((1 / (t : ℝ)) • ∑ s ∈ Finset.Icc 1 t, y (s + 1)) - f xstar
      ≤ β * R ^ 2 / (ρ * t) := by sorry

end ConvexOptAlg.MirrorProx
