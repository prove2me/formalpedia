-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorProx_thm_4_4_first_term
-- name    : ConvexOptAlg.MirrorProx.thm_4_4_first_term
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:22:52.58373+00:00
-- url     : https://prove2.me/theorems/f8863cf9-874d-46f5-b457-5f2ef2e5cba2
-- title:
--   §4.5, proof of Theorem 4.4, p. 306 — first term: η∇f(y_{t+1})⊤(x_{t+1} − x) ≤ D_Φ(x, x_t) − D_Φ(x, x_{t+1}) − D_Φ(x_{t+1}, x_t)
-- statement:
--   In the setting of Chapter 4 ($\mathcal X$ compact convex, $\mathcal D$ convex open with $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\ne\emptyset$, $\Phi$ a mirror map on $\mathcal D$), let $(x_t,y_t,y'_t,x'_t)$ be a run of mirror prox with step size $\eta$ for the gradient map $\nabla f$. Then for every $t\ge1$ and every $x\in\mathcal X\cap\mathcal D$,
--   $$\eta\,\nabla f(y_{t+1})^\top(x_{t+1}-x)\le D_\Phi(x,x_t)-D_\Phi(x,x_{t+1})-D_\Phi(x_{t+1},x_t).$$
--
--   This bounds the first of the three terms into which the proof of Theorem 4.4 splits $\nabla f(y_{t+1})^\top(y_{t+1}-x)$.
--
--   **Formalization Note** The statement holds for every real $\eta$ and does not use any property of $f$ beyond the run, so $f$ itself does not appear; only its gradient map does. The point called $x$ in the book is `u` in Lean, to keep `x` for the iterates.
-- source:
--   Bubeck, arXiv:1405.4980v2, §4.5, proof of Theorem 4.4, p. 306, second display of the proof

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

namespace ConvexOptAlg.MirrorProx

/-- The first term in the proof of Theorem 4.4 (Bubeck, arXiv:1405.4980v2, §4.5, p. 306, second
display of the proof): for a run of mirror prox with step size `η`, every `t ≥ 1` and every
point `u ∈ X ∩ D` (the book's `x`),
`η∇f(y_{t+1})⊤(x_{t+1} − u) ≤ D_Φ(u, x_t) − D_Φ(u, x_{t+1}) − D_Φ(x_{t+1}, x_t)`
(first and last members of the display). -/
theorem thm_4_4_first_term {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (f' : E → E →L[ℝ] ℝ) (η : ℝ) (x y y' x' : ℕ → E)
    (hrun : IsMirrorProxRun X D Φ Φ' f' η x y y' x')
    (t : ℕ) (ht : 1 ≤ t) (u : E) (hu : u ∈ X ∩ D) :
    η * f' (y (t + 1)) (x (t + 1) - u)
      ≤ bregman Φ Φ' u (x t) - bregman Φ Φ' u (x (t + 1))
          - bregman Φ Φ' (x (t + 1)) (x t) := by sorry

end ConvexOptAlg.MirrorProx
