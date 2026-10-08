-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorProx_eq_4_9
-- name    : ConvexOptAlg.MirrorProx.eq_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:23:12.941848+00:00
-- url     : https://prove2.me/theorems/926fa291-38e4-45de-9afa-fb1c5aa05552
-- title:
--   (4.9), proof of Theorem 4.4, p. 307 — second term: η∇f(x_t)⊤(y_{t+1} − x_{t+1}) ≤ D_Φ(x_{t+1}, x_t) − (ρ/2)‖x_{t+1} − y_{t+1}‖² − (ρ/2)‖y_{t+1} − x_t‖²
-- statement:
--   In the setting of Chapter 4, let $\Phi$ be a mirror map on $\mathcal D$ that is $\rho$-strongly convex on $\mathcal X\cap\mathcal D$ with respect to $\|\cdot\|$, and let $(x_t,y_t,y'_t,x'_t)$ be a run of mirror prox with step size $\eta$. Then for every $t\ge1$:
--
--   1. the bound through (4.9):
--   $$\eta\,\nabla f(x_t)^\top(y_{t+1}-x_{t+1})\le D_\Phi(x_{t+1},x_t)-D_\Phi(x_{t+1},y_{t+1})-D_\Phi(y_{t+1},x_t);$$
--   2. the final bound:
--   $$\eta\,\nabla f(x_t)^\top(y_{t+1}-x_{t+1})\le D_\Phi(x_{t+1},x_t)-\frac\rho2\|x_{t+1}-y_{t+1}\|^2-\frac\rho2\|y_{t+1}-x_t\|^2.$$
--
--   This bounds the second of the three terms in the proof of Theorem 4.4; the negative quadratic terms are what absorbs the third term.
--
--   **Formalization Note** No sign condition on $\eta$ or $\rho$ is needed for this display. The dual vector $\nabla f(x_t)$ is the value of the gradient map at $x_t$.
-- source:
--   Bubeck, arXiv:1405.4980v2, §4.5, proof of Theorem 4.4, p. 307, first display, Eq. (4.9)

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

namespace ConvexOptAlg.MirrorProx

/-- The second term in the proof of Theorem 4.4 (Bubeck, arXiv:1405.4980v2, §4.5, p. 307, first
display, through (4.9)): for a run of mirror prox with step size `η`, a mirror map `Φ` that is
`ρ`-strongly convex on `X ∩ D`, and every `t ≥ 1`,
1. `η∇f(x_t)⊤(y_{t+1} − x_{t+1}) ≤ D_Φ(x_{t+1}, x_t) − D_Φ(x_{t+1}, y_{t+1}) − D_Φ(y_{t+1}, x_t)`
   (4.9);
2. `η∇f(x_t)⊤(y_{t+1} − x_{t+1})
     ≤ D_Φ(x_{t+1}, x_t) − (ρ/2)‖x_{t+1} − y_{t+1}‖² − (ρ/2)‖y_{t+1} − x_t‖²`. -/
theorem eq_4_9 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (ρ : ℝ) (hsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' ρ)
    (f' : E → E →L[ℝ] ℝ) (η : ℝ) (x y y' x' : ℕ → E)
    (hrun : IsMirrorProxRun X D Φ Φ' f' η x y y' x')
    (t : ℕ) (ht : 1 ≤ t) :
    η * f' (x t) (y (t + 1) - x (t + 1))
        ≤ bregman Φ Φ' (x (t + 1)) (x t) - bregman Φ Φ' (x (t + 1)) (y (t + 1))
            - bregman Φ Φ' (y (t + 1)) (x t) ∧
      η * f' (x t) (y (t + 1) - x (t + 1))
        ≤ bregman Φ Φ' (x (t + 1)) (x t) - ρ / 2 * ‖x (t + 1) - y (t + 1)‖ ^ 2
            - ρ / 2 * ‖y (t + 1) - x t‖ ^ 2 := by sorry

end ConvexOptAlg.MirrorProx
