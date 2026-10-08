-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorProx_thm_4_4_third_term
-- name    : ConvexOptAlg.MirrorProx.thm_4_4_third_term
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:23:18.833834+00:00
-- url     : https://prove2.me/theorems/16faff5c-8378-4baf-af9d-1da25784515c
-- title:
--   §4.5, proof of Theorem 4.4, p. 307 — third term: (∇f(y_{t+1}) − ∇f(x_t))⊤(y_{t+1} − x_{t+1}) ≤ (β/2)‖y_{t+1} − x_t‖² + (β/2)‖y_{t+1} − x_{t+1}‖²
-- statement:
--   In the setting of Chapter 4, let $f$ be $\beta$-smooth on $\mathcal X$ with respect to $\|\cdot\|$, i.e. $\|\nabla f(x)-\nabla f(y)\|_*\le\beta\|x-y\|$ for $x,y\in\mathcal X$, and let $(x_t,y_t,y'_t,x'_t)$ be a run of mirror prox with step size $\eta$. Then for every $t\ge1$,
--   $$\begin{aligned}
--   (\nabla f(y_{t+1})-\nabla f(x_t))^\top(y_{t+1}-x_{t+1})
--   &\le\|\nabla f(y_{t+1})-\nabla f(x_t)\|_*\cdot\|y_{t+1}-x_{t+1}\|\\
--   &\le\beta\|y_{t+1}-x_t\|\cdot\|y_{t+1}-x_{t+1}\|\\
--   &\le\frac\beta2\|y_{t+1}-x_t\|^2+\frac\beta2\|y_{t+1}-x_{t+1}\|^2 .
--   \end{aligned}$$
--
--   This bounds the third of the three terms in the proof of Theorem 4.4, by the Cauchy–Schwarz inequality for the dual pairing, $\beta$-smoothness, and $2ab\le a^2+b^2$.
--
--   **Formalization Note** The chain is stated as three inequalities. The dual norm $\|\cdot\|_*$ is the operator norm of a continuous linear functional. No sign condition on $\beta$ is assumed: it is forced by the smoothness inequality whenever $\mathcal X$ has two points, and all terms vanish otherwise.
-- source:
--   Bubeck, arXiv:1405.4980v2, §4.5, proof of Theorem 4.4, p. 307, second display

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

namespace ConvexOptAlg.MirrorProx

/-- The third term in the proof of Theorem 4.4 (Bubeck, arXiv:1405.4980v2, §4.5, p. 307, second
display): for a run of mirror prox with step size `η` on a function `f` that is `β`-smooth on `X`
w.r.t. `‖·‖` (gradient map `f'`), and every `t ≥ 1`,
`(∇f(y_{t+1}) − ∇f(x_t))⊤(y_{t+1} − x_{t+1}) ≤ ‖∇f(y_{t+1}) − ∇f(x_t)‖∗ · ‖y_{t+1} − x_{t+1}‖`,
`‖∇f(y_{t+1}) − ∇f(x_t)‖∗ · ‖y_{t+1} − x_{t+1}‖ ≤ β‖y_{t+1} − x_t‖ · ‖y_{t+1} − x_{t+1}‖`, and
`β‖y_{t+1} − x_t‖ · ‖y_{t+1} − x_{t+1}‖ ≤ (β/2)‖y_{t+1} − x_t‖² + (β/2)‖y_{t+1} − x_{t+1}‖²`.
The dual norm `‖·‖∗` is the operator norm on `E →L[ℝ] ℝ`. -/
theorem thm_4_4_third_term {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) (hsm : IsSmoothWRT X f f' β)
    (η : ℝ) (x y y' x' : ℕ → E)
    (hrun : IsMirrorProxRun X D Φ Φ' f' η x y y' x')
    (t : ℕ) (ht : 1 ≤ t) :
    (f' (y (t + 1)) - f' (x t)) (y (t + 1) - x (t + 1))
        ≤ ‖f' (y (t + 1)) - f' (x t)‖ * ‖y (t + 1) - x (t + 1)‖ ∧
      ‖f' (y (t + 1)) - f' (x t)‖ * ‖y (t + 1) - x (t + 1)‖
        ≤ β * ‖y (t + 1) - x t‖ * ‖y (t + 1) - x (t + 1)‖ ∧
      β * ‖y (t + 1) - x t‖ * ‖y (t + 1) - x (t + 1)‖
        ≤ β / 2 * ‖y (t + 1) - x t‖ ^ 2 + β / 2 * ‖y (t + 1) - x (t + 1)‖ ^ 2 := by sorry

end ConvexOptAlg.MirrorProx
