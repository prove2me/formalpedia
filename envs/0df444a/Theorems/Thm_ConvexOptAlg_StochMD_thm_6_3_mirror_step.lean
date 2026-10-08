-- Prove2me | Theorems.Thm_ConvexOptAlg_StochMD_thm_6_3_mirror_step
-- name    : ConvexOptAlg.StochMD.thm_6_3_mirror_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:38:21.475364+00:00
-- url     : https://prove2.me/theorems/c84dccf2-6a47-455b-ac0c-bd6892cff075
-- title:
--   §6.2, proof of Theorem 6.3, p. 333 — the mirror step (1/(β + 1/η)) g̃_s⊤(x_{s+1} − x∗) ≤ D_Φ(x∗, x_s) − D_Φ(x∗, x_{s+1}) − D_Φ(x_{s+1}, x_s)
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $\mathcal D\subseteq E$ and $\Phi$ a mirror map on $\mathcal D$, and $\mathcal X\subseteq E$ convex with $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\neq\emptyset$. Let $\beta\ge0$, $\eta>0$, and put $\gamma=1/(\beta+1/\eta)$. Let $x_s\in\mathcal X\cap\mathcal D$, let $\tilde g_s$ be a linear form, and let $x_{s+1}\in\mathcal X\cap\mathcal D$ be a minimizer over $\mathcal X\cap\mathcal D$ of $x\mapsto\gamma\,\tilde g_s^\top x+D_\Phi(x,x_s)$ (one S-MD step with step size $\gamma$). Then for every $x^*\in\mathcal X$,
--   $$\frac{1}{\beta+1/\eta}\,\tilde g_s^\top(x_{s+1}-x^*)\le D_\Phi(x^*,x_s)-D_\Phi(x^*,x_{s+1})-D_\Phi(x_{s+1},x_s).$$
--
--   This is the inequality the book obtains "using the same argument as to derive (4.9)": the first-order optimality of the mirror step, rewritten through the three-point identity of Bregman divergences.
--
--   **Formalization Note** The book applies the inequality to the minimizer $x^*$ of $f$; the statement holds for every $x^*\in\mathcal X$, including points of $\mathcal X$ on the boundary of $\mathcal D$ (the value $\Phi(x^*)$ cancels in the right-hand side, so the total function $\Phi$ may take any value there). $\beta\ge0$ makes the step size positive.
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.2, proof of Theorem 6.3, second display, p. 333 (referring to (4.9), p. 307)

import Mathlib
import Definitions.Def_ConvexOptAlg_StochMD_Defs

namespace ConvexOptAlg.StochMD

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 6.3, printed p. 333, second display ("using the
same argument as to derive (4.9)"): let `Φ` be a mirror map on `D`, `X` convex with
`X ⊆ closure D` and `X ∩ D ≠ ∅`, `β ≥ 0`, `η > 0`. If `x_s ∈ X ∩ D` and `x_{s+1} ∈ X ∩ D` minimizes
`z ↦ (1/(β + 1/η)) g̃_s⊤z + D_Φ(z, x_s)` over `X ∩ D` (one S-MD step with step size `1/(β + 1/η)`),
then for every `x∗ ∈ X`
`(1/(β + 1/η)) g̃_s⊤(x_{s+1} − x∗) ≤ D_Φ(x∗, x_s) − D_Φ(x∗, x_{s+1}) − D_Φ(x_{s+1}, x_s)`. -/
theorem thm_6_3_mirror_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D) (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (β η : ℝ) (hβ : 0 ≤ β) (hη : 0 < η)
    (xs xs1 : E) (g : E →L[ℝ] ℝ) (hxs : xs ∈ X ∩ D) (hxs1 : xs1 ∈ X ∩ D)
    (hstep : ∀ z ∈ X ∩ D,
      1 / (β + 1 / η) * g xs1 + bregman Φ Φ' xs1 xs ≤ 1 / (β + 1 / η) * g z + bregman Φ Φ' z xs)
    (xstar : E) (hxstar : xstar ∈ X) :
    1 / (β + 1 / η) * g (xs1 - xstar) ≤
      bregman Φ Φ' xstar xs - bregman Φ Φ' xstar xs1 - bregman Φ Φ' xs1 xs := by sorry

end ConvexOptAlg.StochMD
