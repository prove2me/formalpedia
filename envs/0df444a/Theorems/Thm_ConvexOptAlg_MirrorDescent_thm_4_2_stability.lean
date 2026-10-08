-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorDescent_thm_4_2_stability
-- name    : ConvexOptAlg.MirrorDescent.thm_4_2_stability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:03:34.264831+00:00
-- url     : https://prove2.me/theorems/8b160b12-0302-451b-8526-c6606b90d2b6
-- title:
--   §4.2, proof of Theorem 4.2, p. 300 — D_Φ(x_s, y_{s+1}) − D_Φ(x_{s+1}, y_{s+1}) ≤ (ηL)²/(2ρ)
-- statement:
--   Work in the standing setting of Chapter 4, and let the mirror map $\Phi$ be $\rho$-strongly convex on $\mathcal X\cap\mathcal D$ with respect to $\|\cdot\|$, with $\rho>0$. Let $f$ be convex on $\mathcal X$, and let $(x_s,y_s,g_s)$ be a run of mirror descent on $f$ with step size $\eta>0$ for the steps $1,\dots,T$ whose subgradients satisfy $\|g_s\|_*\le L$. Then for every step $1\le s\le T$,
--   $$D_\Phi(x_s,y_{s+1})-D_\Phi(x_{s+1},y_{s+1})\le\frac{(\eta L)^2}{2\rho}.$$
--
--   This bounds the non-telescoping part of the per-step inequality and is where the strong convexity of the mirror map enters the rate.
--
--   **Formalization Note** The book's display is a chain; its first and last members are stated. The page's "$f$ is $L$-Lipschitz" ($\|g\|_*\le L$ for every subgradient at every point of $\mathcal X$) is assumed only for the subgradients the run uses: a weaker hypothesis, hence a stronger statement, and the form that is not vacuous (subgradients relative to $\mathcal X$ are unbounded at boundary points of $\mathcal X$). $\rho>0$ and $\eta>0$ are implicit on the page.
-- source:
--   Bubeck, arXiv:1405.4980v2, §4.2, proof of Theorem 4.2, p. 300, second display

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

namespace ConvexOptAlg.MirrorDescent

/-- Bubeck, §4.2, proof of Theorem 4.2, p. 300 (second display, first and last members): if `Φ` is
`ρ`-strongly convex on `X ∩ D` (`ρ > 0`) `f` is convex on `X`, and the subgradients
the run uses have dual norm `‖g_s‖_* ≤ L` (the page's `L`-Lipschitz assumption), then along a run of
mirror descent with step `η > 0`, for every step `1 ≤ s ≤ T`,
`D_Φ(x_s, y_{s+1}) − D_Φ(x_{s+1}, y_{s+1}) ≤ (ηL)²/(2ρ)`. -/
theorem thm_4_2_stability {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hΦ : IsStronglyConvexMirror X D Φ Φ' ρ)
    (f : E → ℝ) (hf : ConvexOn ℝ X f) (L : ℝ)
    (η : ℝ) (hη : 0 < η) (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ)
    (hgL : ∀ s : ℕ, 1 ≤ s → s ≤ T → ‖g s‖ ≤ L)
    (hrun : IsMirrorDescentRun X D Φ Φ' f η x y g T)
    (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ T) :
    bregman Φ Φ' (x s) (y (s + 1)) - bregman Φ Φ' (x (s + 1)) (y (s + 1)) ≤
      (η * L) ^ 2 / (2 * ρ) := by sorry

end ConvexOptAlg.MirrorDescent
