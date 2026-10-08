-- Prove2me | Theorems.Thm_ConvexOptAlg_StochMD_thm_6_3_smoothness_step
-- name    : ConvexOptAlg.StochMD.thm_6_3_smoothness_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:38:22.84348+00:00
-- url     : https://prove2.me/theorems/6645b8eb-3617-4ba3-8584-b5e81daf538e
-- title:
--   §6.2, proof of Theorem 6.3, pp. 332–333 — f(x_{s+1}) − f(x_s) ≤ g̃_s⊤(x_{s+1} − x_s) + (η/2)‖∇f(x_s) − g̃_s‖²∗ + (β + 1/η)D_Φ(x_{s+1}, x_s)
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, $\mathcal X\subseteq E$ convex and $\mathcal D\subseteq E$. Let $\Phi$ be $1$-strongly convex on $\mathcal X\cap\mathcal D$ with respect to $\|\cdot\|$, and let $f$ be $\beta$-smooth on $\mathcal X$ with respect to $\|\cdot\|$, $\beta\ge0$. Then for any two points $x_s,x_{s+1}\in\mathcal X\cap\mathcal D$, any linear form $\tilde g_s$ and any $\eta>0$,
--   $$f(x_{s+1})-f(x_s)\le\tilde g_s^\top(x_{s+1}-x_s)+\frac{\eta}{2}\|\nabla f(x_s)-\tilde g_s\|_*^2+\Big(\beta+\frac1\eta\Big)D_\Phi(x_{s+1},x_s).$$
--
--   This is the first display of the proof of Theorem 6.3: it splits the progress of one step into a linear term in the stochastic direction, a noise term, and a Bregman term that the mirror step will absorb.
--
--   **Formalization Note** The statement is deterministic: it holds for any points and any linear form, and is applied with $\tilde g_s$ the oracle's answer. The display is stated by its first and last members. $\beta\ge0$ is the nonnegativity of a smoothness constant.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.2, proof of Theorem 6.3, first display, pp. 332–333

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

namespace ConvexOptAlg.StochMD

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 6.3, printed pp. 332–333, first display (first
and last members): if `Φ` is 1-strongly convex on `X ∩ D` and `f` is `β`-smooth on the convex
set `X` w.r.t. `‖·‖`, then for any two points `x_s, x_{s+1} ∈ X ∩ D`, any dual vector `g̃_s` and
any `η > 0`,
`f(x_{s+1}) − f(x_s) ≤ g̃_s⊤(x_{s+1} − x_s) + (η/2)‖∇f(x_s) − g̃_s‖²∗ + (β + 1/η) D_Φ(x_{s+1}, x_s)`. -/
theorem thm_6_3_smoothness_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' 1)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hβ : 0 ≤ β) (hsmooth : IsSmoothWRT X f f' β)
    (η : ℝ) (hη : 0 < η)
    (xs xs1 : E) (hxs : xs ∈ X ∩ D) (hxs1 : xs1 ∈ X ∩ D) (g : E →L[ℝ] ℝ) :
    f xs1 - f xs ≤
      g (xs1 - xs) + η / 2 * ‖f' xs - g‖ ^ 2 + (β + 1 / η) * bregman Φ Φ' xs1 xs := by sorry

end ConvexOptAlg.StochMD
