-- Prove2me | Theorems.Thm_BnBPEP_WeakCvx_theorem_1
-- name    : BnBPEP.WeakCvx.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:13.876558+00:00
-- url     : https://prove2.me/theorems/825dba64-53dd-4611-9174-32239880de6f
-- title:
--   Theorem 1 — potential-function analysis of the subgradient method on $\mathcal W_{1,\widetilde L}$
-- statement:
--   Let $N\in\mathbb N$. Let $L>0$ and let $f\in\mathcal W_{1,L}$ (so $f+\frac12\|\cdot\|^2$ is convex and every subgradient has norm at most $L$) have a global minimizer $x_\star$. Let $R>0$. Consider the subgradient method
--   $$x_{k+1}=x_k-h\,f'(x_k),\qquad k\in[0:N],$$
--   where $f'(x_k)\in\partial f(x_k)$ is an arbitrary subgradient of $f$ at $x_k$. Let $y_k=\mathrm{prox}_{(1/2)f}(x_k)$ for $k\in[0:N+1]$, $f'(y_k)=2(x_k-y_k)$, assume the initial condition $f(y_0)-f(x_\star)+\|x_0-y_0\|^2\le R^2$, and let
--   $$\psi_k=b_k\big(f(y_k)-f(x_\star)+\|x_k-y_k\|^2\big),\qquad k\in[0:N+1].$$
--   If $h\in(0,\tfrac12]$, $4+(1-2h)b_{k+1}=b_k$ for $k\in[0:N]$, $b_{N+1}=0$, and $c_k=h^2b_{k+1}$ for $k\in[0:N]$, then
--   $$\|f'(y_k)\|^2+\psi_{k+1}-\psi_k\le c_k\|f'(x_k)\|^2\qquad\text{for all }k\in[0:N],$$
--   and
--   $$\frac{1}{N+1}\sum_{i=0}^{N}\|\nabla f_{(1/2)}(x_i)\|^2\ \le\ \frac{1}{N+1}\Big(L^2\sum_{i=0}^{N}c_i+b_0R^2\Big),$$
--   where $f_{(1/2)}(x)=\min_y\{f(y)+\|y-x\|^2\}$ is the Moreau envelope.
--
--   This is the main analytical result of the paper: a rate for the averaged squared Moreau-envelope gradient of the subgradient method on nonsmooth, nonconvex (weakly convex) functions, discovered with the BnB-PEP methodology. Corollary 1 obtains an explicit rate by choosing $h$.
--
--   **Formalization Note** $L$ is the paper's $\widetilde L$ (the subgradient bound after normalizing the weak-convexity modulus to $\rho=1$; the general class $\mathcal W_{\rho,L}$ reduces to this one by scaling $f/\rho$, which is not stated). The parameters $b$ and $c$ are pinned by the hypotheses, not chosen. The prox points are hypotheses `IsProxPoint f (1/2) (x k) (y k)`; $\|f'(y_k)\|^2$ is written $\|2(x_k-y_k)\|^2$, and the averaged bound uses the gradient of the real-valued Moreau envelope `moreauEnv 2 f`. Subgradients are those of the weak-convexity inequality with modulus $1$.
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.3, p. 623, Theorem 1

import Mathlib
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_BnBPEP_WeakCvx_IsWeakSubgrad
import Definitions.Def_BnBPEP_WeakCvx_InWeakClass
import Definitions.Def_BnBPEP_WeakCvx_moreauEnv

namespace BnBPEP.WeakCvx

/-- Theorem 1, p. 623: potential-function analysis of the subgradient method
`x_{k+1} = x_k - h f'(x_k)` on `W_{1,L}` (the paper's `W_{1,L̃}`), with arbitrary subgradients
`f'(x_k) = g_k`, prox points `y_k = prox_{(1/2)f}(x_k)`, `f'(y_k) = 2(x_k - y_k)`, and the
parameters `4 + (1 - 2h) b_{k+1} = b_k`, `b_{N+1} = 0`, `c_k = h² b_{k+1}`, `h ∈ (0, 1/2]`. -/
theorem theorem_1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (hL : 0 < L) (hf : InWeakClass 1 L f)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ z, f xstar ≤ f z)
    (R : ℝ) (hR : 0 < R) (N : ℕ) (h : ℝ)
    (x g y : ℕ → EuclideanSpace ℝ (Fin d))
    (hg : ∀ k ≤ N, IsWeakSubgrad 1 f (x k) (g k))
    (hstep : ∀ k ≤ N, x (k + 1) = x k - h • g k)
    (hy : ∀ k ≤ N + 1, SAGA.Convex.IsProxPoint f (1 / 2) (x k) (y k))
    (hinit : f (y 0) - f xstar + ‖x 0 - y 0‖ ^ 2 ≤ R ^ 2)
    (b c : ℕ → ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 2)
    (hrec : ∀ k ≤ N, 4 + (1 - 2 * h) * b (k + 1) = b k) (hterm : b (N + 1) = 0)
    (hc : ∀ k ≤ N, c k = h ^ 2 * b (k + 1)) :
    (∀ k ≤ N,
      ‖(2 : ℝ) • (x k - y k)‖ ^ 2
          + b (k + 1) * (f (y (k + 1)) - f xstar + ‖x (k + 1) - y (k + 1)‖ ^ 2)
          - b k * (f (y k) - f xstar + ‖x k - y k‖ ^ 2)
        ≤ c k * ‖g k‖ ^ 2) ∧
      1 / ((N : ℝ) + 1) * ∑ i ∈ Finset.range (N + 1), ‖gradient (moreauEnv 2 f) (x i)‖ ^ 2
        ≤ 1 / ((N : ℝ) + 1) * (L ^ 2 * ∑ i ∈ Finset.range (N + 1), c i + b 0 * R ^ 2) := by sorry

end BnBPEP.WeakCvx
