-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorProx_thm_4_4_per_step
-- name    : ConvexOptAlg.MirrorProx.thm_4_4_per_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:23:26.0382+00:00
-- url     : https://prove2.me/theorems/3dd31818-2aed-437c-9303-c34d14bc470e
-- title:
--   §4.5, proof of Theorem 4.4, p. 307 — per-step bound f(y_{t+1}) − f(x) ≤ (D_Φ(x, x_t) − D_Φ(x, x_{t+1}))/η for η = ρ/β
-- statement:
--   In the setting of Chapter 4, let $\Phi$ be a mirror map on $\mathcal D$ that is $\rho$-strongly convex on $\mathcal X\cap\mathcal D$ with respect to $\|\cdot\|$ ($\rho>0$), and let $f$ be convex and $\beta$-smooth on $\mathcal X$ with respect to $\|\cdot\|$ ($\beta>0$). Let $(x_t,y_t,y'_t,x'_t)$ be a run of mirror prox with step size $\eta=\rho/\beta$. Then for every $t\ge1$ and every $x\in\mathcal X\cap\mathcal D$,
--   $$f(y_{t+1})-f(x)\le\frac{D_\Phi(x,x_t)-D_\Phi(x,x_{t+1})}{\eta}.$$
--
--   Summing this bound over $t$ telescopes the right-hand side; together with convexity of $f$ this gives Theorem 4.4.
--
--   **Formalization Note** $\rho>0$ and $\beta>0$ are the implicit conditions under which $\eta=\rho/\beta$ is a step size; in Lean a division by $0$ would return $0$. The point called $x$ in the book is `u` in Lean.
-- source:
--   Bubeck, arXiv:1405.4980v2, §4.5, proof of Theorem 4.4, p. 307, last display

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

namespace ConvexOptAlg.MirrorProx

/-- The per-step bound in the proof of Theorem 4.4 (Bubeck, arXiv:1405.4980v2, §4.5, p. 307, last
display): let `Φ` be a mirror map `ρ`-strongly convex on `X ∩ D` (`ρ > 0`) and `f` convex and
`β`-smooth on `X` w.r.t. `‖·‖` (`β > 0`). For a run of mirror prox with `η = ρ/β`, every `t ≥ 1`
and every `u ∈ X ∩ D` (the book's `x`),
`f(y_{t+1}) − f(u) ≤ (D_Φ(u, x_t) − D_Φ(u, x_{t+1})) / η`. -/
theorem thm_4_4_per_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' ρ)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (hf : ConvexOn ℝ X f)
    (β : ℝ) (hβ : 0 < β) (hsm : IsSmoothWRT X f f' β)
    (x y y' x' : ℕ → E) (hrun : IsMirrorProxRun X D Φ Φ' f' (ρ / β) x y y' x')
    (t : ℕ) (ht : 1 ≤ t) (u : E) (hu : u ∈ X ∩ D) :
    f (y (t + 1)) - f u
      ≤ (bregman Φ Φ' u (x t) - bregman Φ Φ' u (x (t + 1))) / (ρ / β) := by sorry

end ConvexOptAlg.MirrorProx
