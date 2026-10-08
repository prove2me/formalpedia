-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorDescent_thm_4_2_sum
-- name    : ConvexOptAlg.MirrorDescent.thm_4_2_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:03:42.686195+00:00
-- url     : https://prove2.me/theorems/8700c4ee-96cf-4f9e-9039-f5f1a62c560b
-- title:
--   §4.2, proof of Theorem 4.2, p. 300 — Σ_{s=1}^t (f(x_s) − f(x)) ≤ D_Φ(x, x₁)/η + ηL²t/(2ρ)
-- statement:
--   Work in the standing setting of Chapter 4, and let the mirror map $\Phi$ be $\rho$-strongly convex on $\mathcal X\cap\mathcal D$ with $\rho>0$. Let $f$ be convex on $\mathcal X$, let $t\ge1$, and let $(x_s,y_s,g_s)$ be a run of mirror descent on $f$ with step size $\eta>0$ for the steps $1,\dots,t$ whose subgradients satisfy $\|g_s\|_*\le L$. Then for every $x\in\mathcal X\cap\mathcal D$,
--   $$\sum_{s=1}^{t}\big(f(x_s)-f(x)\big)\le\frac{D_\Phi(x,x_1)}{\eta}+\eta\frac{L^2t}{2\rho}.$$
--
--   Theorem 4.2 follows from this bound by Jensen's inequality, the bound $D_\Phi(x,x_1)\le R^2$, the choice of $\eta$, and a limit $x\to x^*$.
--
--   **Formalization Note** The $L$ bound is assumed only for the subgradients the run uses (see the stability bound). $\rho>0$ and $\eta>0$ are implicit on the page.
-- source:
--   Bubeck, arXiv:1405.4980v2, §4.2, proof of Theorem 4.2, p. 300, last display

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

namespace ConvexOptAlg.MirrorDescent

/-- Bubeck, §4.2, proof of Theorem 4.2, p. 300 (last display, "We proved"): if `Φ` is `ρ`-strongly
convex on `X ∩ D` (`ρ > 0`) `f` is convex on `X`, and the subgradients
the run uses have dual norm `‖g_s‖_* ≤ L` (the page's `L`-Lipschitz assumption), then along a run of mirror
descent with step `η > 0` for the steps `1, …, t` (`t ≥ 1`), for every `x ∈ X ∩ D`,
`∑_{s=1}^t (f(x_s) − f(x)) ≤ D_Φ(x, x_1)/η + η L² t/(2ρ)`. -/
theorem thm_4_2_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ)
    (f : E → ℝ) (hf : ConvexOn ℝ X f) (L : ℝ)
    (η : ℝ) (hη : 0 < η) (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hgL : ∀ s : ℕ, 1 ≤ s → s ≤ t → ‖g s‖ ≤ L)
    (hrun : IsMirrorDescentRun X D Φ Φ' f η x y g t)
    (u : E) (hu : u ∈ X ∩ D) :
    ∑ s ∈ Finset.Icc 1 t, (f (x s) - f u) ≤
      bregman Φ Φ' u (x 1) / η + η * (L ^ 2 * t / (2 * ρ)) := by sorry

end ConvexOptAlg.MirrorDescent
