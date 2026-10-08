-- Prove2me | Theorems.Thm_Dubey1986_Inefficiency_Dmap_linear_perturbation
-- name    : Dubey1986.Inefficiency.Dmap_linear_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:35.47257+00:00
-- url     : https://prove2.me/theorems/fb9f9ff4-8f62-4201-8583-c7f8eba693ae
-- title:
--   p. 5, (**) — adding $t\sum_j y_{ij}x_j$ to $u^i$ moves $D(u,s)$ by $t\,y$
-- statement:
--   Let $u_0\in(U)^n$ be a game, $s_0\in V$, and let $y$ be an arbitrary $n\times r(n)$ matrix with rows $y_i$. For $t\in\mathbb R$ define the perturbed payoffs
--   $$u_t^i(x)=u_0^i(x)+\sum_{j=1}^{r(n)} t\,y_{ij}x_j .$$
--   Then for every $t$,
--   $$D(u_t,s_0)=D(u_0,s_0)+t\,y,$$
--   and consequently $\frac{d}{dt}D(u_t,s_0)\big|_{t=0}=y$.
--
--   This is the computation on p. 5 verifying (**): $D$ is transverse to every submanifold of $\mathbb R^{n\times r(n)}$, which by the transversal density and openness theorems yields (*).
--
--   **Formalization Note** The perturbed payoffs are not required to lie in $(U)^n$: a linear function has finite $C^2$-norm on $V$ only if $V$ is bounded, which the paper does not assume; the identity concerns derivatives at $s_0$ only.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 5, the path (u_t, s_t) and the display verifying (**)

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

namespace Dubey1986.Inefficiency

theorem Dmap_linear_perturbation {n : ℕ} (k : Fin n → ℕ)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (u₀ : Fin n → Strat k → ℝ) (hu₀ : IsGame V u₀) (s₀ : Strat k) (hs₀ : s₀ ∈ Vset V)
    (y : Fin n → (Strat k →L[ℝ] ℝ)) :
    (∀ t : ℝ, Dmap (fun i x => u₀ i x + t * y i x) s₀ = Dmap u₀ s₀ + t • y) ∧
    HasDerivAt (fun t : ℝ => Dmap (fun i x => u₀ i x + t * y i x) s₀) y 0 := by sorry

end Dubey1986.Inefficiency
