-- Prove2me | Theorems.Thm_ConvexOptAlg_StochMD_thm_6_3_pathwise
-- name    : ConvexOptAlg.StochMD.thm_6_3_pathwise
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:38:52.210896+00:00
-- url     : https://prove2.me/theorems/f7b0f506-7d11-47a5-a08c-635958b5caf1
-- title:
--   §6.2, proof of Theorem 6.3, p. 333 — pathwise bound f(x_{s+1}) ≤ f(x∗) + (g̃_s − ∇f(x_s))⊤(x∗ − x_s) + (β + 1/η)(D_Φ(x∗, x_s) − D_Φ(x∗, x_{s+1})) + (η/2)‖∇f(x_s) − g̃_s‖²∗
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $\Phi$ a mirror map on $\mathcal D\subseteq E$, $\mathcal X\subseteq E$ convex with $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\ne\emptyset$, and $\Phi$ $1$-strongly convex on $\mathcal X\cap\mathcal D$ with respect to $\|\cdot\|$. Let $f$ be convex and $\beta$-smooth on $\mathcal X$ with respect to $\|\cdot\|$, $\beta\ge0$, and $\eta>0$. Let $x_s\in\mathcal X\cap\mathcal D$, $\tilde g_s$ a linear form, and $x_{s+1}\in\mathcal X\cap\mathcal D$ a minimizer over $\mathcal X\cap\mathcal D$ of $x\mapsto\frac{1}{\beta+1/\eta}\tilde g_s^\top x+D_\Phi(x,x_s)$. Write $\Delta_s=D_\Phi(x^*,x_s)-D_\Phi(x^*,x_{s+1})$. Then for every $x^*\in\mathcal X$,
--   $$\begin{aligned}f(x_{s+1})&\le f(x_s)+\tilde g_s^\top(x^*-x_s)+\Big(\beta+\frac1\eta\Big)\Delta_s+\frac\eta2\|\nabla f(x_s)-\tilde g_s\|_*^2\\&\le f(x^*)+(\tilde g_s-\nabla f(x_s))^\top(x^*-x_s)+\Big(\beta+\frac1\eta\Big)\Delta_s+\frac\eta2\|\nabla f(x_s)-\tilde g_s\|_*^2.\end{aligned}$$
--
--   This combines the smoothness step and the mirror step into a bound on the value at the new iterate that holds for every realisation of the oracle; the cross term $(\tilde g_s-\nabla f(x_s))^\top(x^*-x_s)$ is the one that vanishes in expectation.
--
--   **Formalization Note** The two inequalities of the display are stated as a conjunction. The book applies them to the minimizer $x^*$ of $f$; they hold for every $x^*\in\mathcal X$. $\beta\ge0$ is the nonnegativity of a smoothness constant.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.2, proof of Theorem 6.3, third display, p. 333

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

namespace ConvexOptAlg.StochMD

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 6.3, printed p. 333, third display ("Thus …"):
in the setting of Theorem 6.3 (`Φ` a mirror map 1-strongly convex on `X ∩ D`, `f` convex and
`β`-smooth on the convex set `X`), if `x_s ∈ X ∩ D` and `x_{s+1} ∈ X ∩ D` is the S-MD step from `x_s`
with direction `g̃_s` and step size `1/(β + 1/η)`, then for every `x∗ ∈ X`
`f(x_{s+1}) ≤ f(x_s) + g̃_s⊤(x∗ − x_s) + (β + 1/η)(D_Φ(x∗, x_s) − D_Φ(x∗, x_{s+1})) + (η/2)‖∇f(x_s) − g̃_s‖²∗`
and the right-hand side is at most
`f(x∗) + (g̃_s − ∇f(x_s))⊤(x∗ − x_s) + (β + 1/η)(D_Φ(x∗, x_s) − D_Φ(x∗, x_{s+1})) + (η/2)‖∇f(x_s) − g̃_s‖²∗`. -/
theorem thm_6_3_pathwise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D) (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (hf : ConvexOn ℝ X f) (hsmooth : IsSmoothWRT X f f' β)
    (η : ℝ) (hη : 0 < η)
    (xs xs1 : E) (g : E →L[ℝ] ℝ) (hxs : xs ∈ X ∩ D) (hxs1 : xs1 ∈ X ∩ D)
    (hstep : ∀ z ∈ X ∩ D,
      1 / (β + 1 / η) * g xs1 + bregman Φ Φ' xs1 xs ≤ 1 / (β + 1 / η) * g z + bregman Φ Φ' z xs)
    (xstar : E) (hxstar : xstar ∈ X) :
    f xs1 ≤ f xs + g (xstar - xs) +
        (β + 1 / η) * (bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1) +
        η / 2 * ‖f' xs - g‖ ^ 2 ∧
      f xs + g (xstar - xs) +
          (β + 1 / η) * (bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1) +
          η / 2 * ‖f' xs - g‖ ^ 2 ≤
        f xstar + (g - f' xs) (xstar - xs) +
          (β + 1 / η) * (bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1) +
          η / 2 * ‖f' xs - g‖ ^ 2 := by sorry

end ConvexOptAlg.StochMD
