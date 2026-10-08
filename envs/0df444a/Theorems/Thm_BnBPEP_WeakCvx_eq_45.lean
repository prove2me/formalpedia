-- Prove2me | Theorems.Thm_BnBPEP_WeakCvx_eq_45
-- name    : BnBPEP.WeakCvx.eq_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:00.804413+00:00
-- url     : https://prove2.me/theorems/0b445e7e-735a-48ef-9576-c18f3ad904bc
-- title:
--   (45) — the bound of Theorem 1 as an explicit function of $h$
-- statement:
--   Let $N\in\mathbb N$, $h\in(0,\tfrac12]$, $L>0$ and $\kappa\in\mathbb R$. Let $b_0,\dots,b_{N+1}$ and $c_0,\dots,c_N$ be the parameters of Theorem 1: $4+(1-2h)b_{k+1}=b_k$ for $k\in[0:N]$, $b_{N+1}=0$, and $c_k=h^2b_{k+1}$. Then
--   $$\frac{L^2}{N+1}\Big(\sum_{i=0}^{N}c_i+\kappa^2b_0\Big)=\frac{L^2}{N+1}\Big[-1+(1-2h)^{N+1}+2h(N+1)+\kappa^2\,\frac{2}{h}\Big(1-(1-2h)^{N+1}\Big)\Big].\tag{45}$$
--
--   With $\kappa=R/L$, the left-hand side is the right-hand side $\frac1{N+1}\big(L^2\sum c_i+b_0R^2\big)$ of Theorem 1, since $L^2\kappa^2b_0=b_0R^2$. The identity thus expresses the guarantee of Theorem 1 in closed form as a function of the stepsize $h$, which is the quantity to be minimized.
--
--   **Formalization Note** $L$ is the paper's $\widetilde L$; $\kappa$ is a free real parameter (the paper's $\kappa=R/\widetilde L$).
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.3, p. 624, (45)

import Mathlib

namespace BnBPEP.WeakCvx

/-- (45), p. 624: with `b, c` as in Theorem 1 (so `b` is given by (44)) and `κ = R/L`,
`(L²/(N+1)) (Σ_{i=0}^N c_i + κ² b_0)
  = (L²/(N+1)) [-1 + (1 - 2h)^{N+1} + 2h(N+1) + κ² (2/h)(1 - (1 - 2h)^{N+1})]`. -/
theorem eq_45 (N : ℕ) (h L κ : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 2) (hL : 0 < L) (b c : ℕ → ℝ)
    (hrec : ∀ k ≤ N, 4 + (1 - 2 * h) * b (k + 1) = b k) (hterm : b (N + 1) = 0)
    (hc : ∀ k ≤ N, c k = h ^ 2 * b (k + 1)) :
    L ^ 2 / ((N : ℝ) + 1) * (∑ i ∈ Finset.range (N + 1), c i + κ ^ 2 * b 0)
      = L ^ 2 / ((N : ℝ) + 1) * (-1 + (1 - 2 * h) ^ (N + 1) + 2 * h * ((N : ℝ) + 1)
          + κ ^ 2 * (2 / h) * (1 - (1 - 2 * h) ^ (N + 1))) := by sorry

end BnBPEP.WeakCvx
