-- Prove2me | Theorems.Thm_BnBPEP_WeakCvx_eq_44_closed_form
-- name    : BnBPEP.WeakCvx.eq_44_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:57.584413+00:00
-- url     : https://prove2.me/theorems/06184984-0718-45b2-b6e4-58dcc4d01fa4
-- title:
--   (44) — $b_k=\frac2h\big(1-(1-2h)^{N+1-k}\big)$ and nonnegativity of the multipliers
-- statement:
--   Let $N\in\mathbb N$ and $h\in(0,\tfrac12]$. Let $b_0,\dots,b_{N+1}$ satisfy the recursion of (43) with terminal condition,
--   $$4+(1-2h)\,b_{k+1}=b_k\quad(k\in[0:N]),\qquad b_{N+1}=0.$$
--   Then
--   $$b_k=\frac{2}{h}\Big(1-(1-2h)^{N+1-k}\Big)\qquad\text{for } k\in[0:N+1],\tag{44}$$
--   and the resulting values of (43) are nonnegative:
--
--   1. $b_k\ge0$ for $k\in[0:N+1]$;
--   2. for $k\in[0:N]$: $c_k=h^2b_{k+1}\ge0$, $\lambda^{[k]}_{2,3}=b_{k+1}\ge0$, $\lambda^{[k]}_{2,0}=\lambda^{[k]}_{0,2}=2hb_{k+1}\ge0$, and $\tau^{[k]}_2=b_k-b_{k+1}\ge0$.
--
--   The closed form makes the bound of Theorem 1 explicit in $h$, and the nonnegativity is what makes the weights of the potential-function proof admissible.
--
--   **Formalization Note** The multipliers $\lambda$, $\tau$ of the QCQP (42) are not formalized; their values from (43) appear as the bare expressions $b_{k+1}$, $2hb_{k+1}$, $b_k-b_{k+1}$. The exponent $N+1-k$ is natural-number subtraction, exact for $k\le N+1$.
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.3, pp. 622–623, (44); (43) on p. 622

import Mathlib

namespace BnBPEP.WeakCvx

/-- (44), p. 623: for `h ∈ (0, 1/2]`, the recursion `4 + (1 - 2h) b_{k+1} = b_k` (`k ∈ [0 : N]`)
of (43) with `b_{N+1} = 0` gives `b_k = (2/h)(1 - (1 - 2h)^{N+1-k})` for `k ∈ [0 : N+1]`, and the
values `b_k`, `c_k = h² b_{k+1}`, `λ_{2,3} = b_{k+1}`, `λ_{2,0} = λ_{0,2} = 2h b_{k+1}`,
`τ_2 = b_k - b_{k+1}` of (43) are nonnegative. -/
theorem eq_44_closed_form (N : ℕ) (h : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 2) (b : ℕ → ℝ)
    (hrec : ∀ k ≤ N, 4 + (1 - 2 * h) * b (k + 1) = b k) (hterm : b (N + 1) = 0) :
    (∀ k ≤ N + 1, b k = 2 / h * (1 - (1 - 2 * h) ^ (N + 1 - k)) ∧ 0 ≤ b k) ∧
      (∀ k ≤ N, 0 ≤ h ^ 2 * b (k + 1) ∧ 0 ≤ 2 * h * b (k + 1) ∧ 0 ≤ b k - b (k + 1)) := by sorry

end BnBPEP.WeakCvx
