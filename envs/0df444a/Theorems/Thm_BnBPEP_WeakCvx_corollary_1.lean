-- Prove2me | Theorems.Thm_BnBPEP_WeakCvx_corollary_1
-- name    : BnBPEP.WeakCvx.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:16.496456+00:00
-- url     : https://prove2.me/theorems/2e72c0f1-db3d-4d65-a6d7-2cc118ed4b13
-- title:
--   Corollary 1 — subgradient rate $\widetilde L^2(2\sqrt{4\kappa^2(N+1)+1}-1)/(N+1)$ on weakly convex functions
-- statement:
--   Let $N\in\mathbb N$, $L>0$, and let $f\in\mathcal W_{1,L}$ ($f+\frac12\|\cdot\|^2$ convex, all subgradients of norm at most $L$) have a global minimizer $x_\star$. Let $R>0$ and $\kappa=R/L$. Run the subgradient method
--   $$x_{k+1}=x_k-h\,f'(x_k),\qquad k\in[0:N],$$
--   with arbitrary subgradients $f'(x_k)\in\partial f(x_k)$ and the stepsize
--   $$h=\frac{\sqrt{4\kappa^2(N+1)+1}}{2(N+1)},$$
--   and assume, as in the setup of Theorem 1, that $h\le\tfrac12$. Let $y_k=\mathrm{prox}_{(1/2)f}(x_k)$ for $k\in[0:N+1]$ and assume the initial condition $f(y_0)-f(x_\star)+\|x_0-y_0\|^2\le R^2$. Then
--   $$\frac{1}{N+1}\sum_{i=0}^{N}\|\nabla f_{(1/2)}(x_i)\|^2\ \le\ \frac{L^2\big(2\sqrt{4\kappa^2(N+1)+1}-1\big)}{N+1},$$
--   where $f_{(1/2)}(x)=\min_y\{f(y)+\|y-x\|^2\}$ is the Moreau envelope of $f$.
--
--   This is the explicit rate of the subgradient method on nonsmooth weakly convex functions obtained by Das Gupta, Van Parys and Ryu with the BnB-PEP methodology; it improves on the rate $L^2\,4\kappa/\sqrt{N+1}$ of Davis and Drusvyatskiy for all large enough $N$. Since the minimum of the summands is at most their average, it also bounds $\min_{i\in[0:N]}\|\nabla f_{(1/2)}(x_i)\|^2$.
--
--   **Formalization Note** "In the setup of Theorem 1" includes Theorem 1's requirement $h\in(0,\frac12]$; for this stepsize it reads $4\kappa^2(N+1)+1\le(N+1)^2$ and is stated as the explicit hypothesis $h\le\frac12$ (it fails, e.g., for $N=0$). $L$ is the paper's $\widetilde L$ (normalized weak-convexity modulus $\rho=1$), and $\kappa=R/L$ is written inline. The prox points are hypotheses `IsProxPoint f (1/2) (x k) (y k)`, the subdifferential is the weak-convexity inequality with modulus $1$, and $\nabla f_{(1/2)}$ is the gradient of the real-valued Moreau envelope `moreauEnv 2 f`.
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.3, p. 625, Corollary 1 (κ = R/L defined on p. 624, L the normalized bound L̃)

import Mathlib
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_BnBPEP_WeakCvx_IsWeakSubgrad
import Definitions.Def_BnBPEP_WeakCvx_InWeakClass
import Definitions.Def_BnBPEP_WeakCvx_moreauEnv

namespace BnBPEP.WeakCvx

/-- Corollary 1, p. 625: in the setup of Theorem 1 (which requires `h ∈ (0, 1/2]`), the stepsize
`h = √(4κ²(N+1) + 1) / (2(N+1))` with `κ = R/L` yields
`(1/(N+1)) Σ_{i=0}^N ‖∇f_{(1/2)}(x_i)‖² ≤ L² (2√(4κ²(N+1) + 1) - 1)/(N+1)`.
Here `L` is the paper's `L̃` (subgradient bound after normalizing `ρ = 1`). -/
theorem corollary_1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (hL : 0 < L) (hf : InWeakClass 1 L f)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ z, f xstar ≤ f z)
    (R : ℝ) (hR : 0 < R) (N : ℕ) (h : ℝ)
    (hhdef : h = √(4 * (R / L) ^ 2 * ((N : ℝ) + 1) + 1) / (2 * ((N : ℝ) + 1)))
    (hh : h ≤ 1 / 2)
    (x g y : ℕ → EuclideanSpace ℝ (Fin d))
    (hg : ∀ k ≤ N, IsWeakSubgrad 1 f (x k) (g k))
    (hstep : ∀ k ≤ N, x (k + 1) = x k - h • g k)
    (hy : ∀ k ≤ N + 1, SAGA.Convex.IsProxPoint f (1 / 2) (x k) (y k))
    (hinit : f (y 0) - f xstar + ‖x 0 - y 0‖ ^ 2 ≤ R ^ 2) :
    1 / ((N : ℝ) + 1) * ∑ i ∈ Finset.range (N + 1), ‖gradient (moreauEnv 2 f) (x i)‖ ^ 2
      ≤ L ^ 2 * (2 * √(4 * (R / L) ^ 2 * ((N : ℝ) + 1) + 1) - 1) / ((N : ℝ) + 1) := by sorry

end BnBPEP.WeakCvx
