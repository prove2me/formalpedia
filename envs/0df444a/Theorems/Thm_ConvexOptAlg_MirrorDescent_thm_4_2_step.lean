-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorDescent_thm_4_2_step
-- name    : ConvexOptAlg.MirrorDescent.thm_4_2_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:03:25.601143+00:00
-- url     : https://prove2.me/theorems/1089097f-7856-4ce0-a10c-c5923162a506
-- title:
--   §4.2, proof of Theorem 4.2, p. 300 — per-step inequality f(x_s) − f(x) ≤ (1/η)(D_Φ(x,x_s) + D_Φ(x_s,y_{s+1}) − D_Φ(x,x_{s+1}) − D_Φ(x_{s+1},y_{s+1}))
-- statement:
--   Work in the standing setting of Chapter 4 ($\mathcal X$ compact convex, $\Phi$ a mirror map on $\mathcal D$, $\mathcal X\subseteq\overline{\mathcal D}$, $\mathcal X\cap\mathcal D\ne\emptyset$), and let $f$ be convex on $\mathcal X$. Let $(x_s,y_s,g_s)$ be a run of mirror descent on $f$ with step size $\eta>0$ for the steps $1,\dots,T$. Then for every step $1\le s\le T$ and every $x\in\mathcal X\cap\mathcal D$,
--   $$f(x_s)-f(x)\le\frac1\eta\Big(D_\Phi(x,x_s)+D_\Phi(x_s,y_{s+1})-D_\Phi(x,x_{s+1})-D_\Phi(x_{s+1},y_{s+1})\Big).$$
--
--   This is the one-step inequality of the analysis of mirror descent: summed over $s$, the terms $D_\Phi(x,x_s)-D_\Phi(x,x_{s+1})$ telescope.
--
--   **Formalization Note** The book's display is a chain; its first and last members are stated. $\eta>0$ is the step size of the method (the bound divides by $\eta$).
-- source:
--   Bubeck, arXiv:1405.4980v2, §4.2, proof of Theorem 4.2, p. 300, first display

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

namespace ConvexOptAlg.MirrorDescent

/-- Bubeck, §4.2, proof of Theorem 4.2, p. 300 (first display, first and last members): along a run
of mirror descent with step `η > 0` on a convex `f`, for every step `1 ≤ s ≤ T` and every
`x ∈ X ∩ D`,
`f(x_s) − f(x) ≤ (1/η)(D_Φ(x, x_s) + D_Φ(x_s, y_{s+1}) − D_Φ(x, x_{s+1}) − D_Φ(x_{s+1}, y_{s+1}))`. -/
theorem thm_4_2_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (f : E → ℝ) (hf : ConvexOn ℝ X f)
    (η : ℝ) (hη : 0 < η) (x y : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ)
    (hrun : IsMirrorDescentRun X D Φ Φ' f η x y g T)
    (s : ℕ) (hs1 : 1 ≤ s) (hsT : s ≤ T) (u : E) (hu : u ∈ X ∩ D) :
    f (x s) - f u ≤
      (1 / η) * (bregman Φ Φ' u (x s) + bregman Φ Φ' (x s) (y (s + 1))
        - bregman Φ Φ' u (x (s + 1)) - bregman Φ Φ' (x (s + 1)) (y (s + 1))) := by sorry

end ConvexOptAlg.MirrorDescent
