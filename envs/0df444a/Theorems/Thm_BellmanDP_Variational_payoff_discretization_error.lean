-- Prove2me | Theorems.Thm_BellmanDP_Variational_payoff_discretization_error
-- name    : BellmanDP.Variational.payoff_discretization_error
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T19:37:21.349008+00:00
-- url     : https://prove2.me/theorems/c9eddaa3-c172-4007-bc03-f61e0875aa98
-- title:
--   Chapter IX, § 12, Eq. (12.13) — $|J(\varphi)-J_N(\{\varphi_k\},n)|\le B'/n$ for step controls
-- statement:
--   Let $F(x,y)$ and $G(x,y)$ satisfy the assumptions (11) of Chapter IX, Theorem 2, and write $\tilde F(x,\varphi)=F(x,\varphi x)$, $\tilde G(x,\varphi)=G(x,\varphi x)$. Let $c>0$ and $T>0$. Then there is a constant $B'$, depending only on $c$, $T$, $F$ and $G$, such that for every $n\ge 1$ and every discrete control $\varphi_0,\dots,\varphi_N\in[0,1]$, $N=\lfloor Tn\rfloor$, with associated step function $\varphi(t)=\varphi_k$ on $k/n\le t<(k+1)/n$,
--   $$\bigl|J(\varphi)-J_N(\{\varphi_k\},n)\bigr|\le\frac{B'}{n}.$$
--   Here $J(\varphi)=\int_0^T\tilde F(x(t),\varphi(t))\,dt$ along any solution of $dx/dt=\tilde G(x,\varphi)$, $x(0)=c$, on $[0,T]$, and $J_N(\{\varphi_k\},n)=\sum_{k=0}^{N}\tilde F(x_k,\varphi_k)/n$ with $x_0=c$, $x_{k+1}=x_k+\tilde G(x_k,\varphi_k)/n$.
--
--   The estimate compares a discrete control with the continuous control it induces; both halves of the convergence proof of Theorem 2 rest on it.
--
--   **Formalization Note** The print names the constant $B_1$ and then writes $B'$ in the display; they are the same constant. The step count is the corrected $N=\lfloor Tn\rfloor$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IX, § 12, proof of Theorem 2, Eq. (12.13), p. 262

import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation

namespace BellmanDP.Variational

open Set

/-- Bellman, *Dynamic Programming*, Ch. IX, § 12, proof of Theorem 2, Eq. (12.13), p. 262: under the
assumptions (11) on `F (x, y)`, `G (x, y)`, for `c > 0` and `T > 0` there is a constant `B′`
(depending only on `c, T, F, G`) such that for every `n ≥ 1` and every step control
`φ (t) = φ_k` on `k/n ≤ t < (k+1)/n` with `0 ≤ φ_k ≤ 1`,
`|J (φ) − J_N ({φ_k}, n)| ≤ B′ / n`, where `J (φ) = ∫_0^T F (x, φ x) dt` along the solution of
`dx/dt = G (x, φ x)`, `x (0) = c`, and `N = ⌊T n⌋`. -/
theorem payoff_discretization_error (F G : ℝ → ℝ → ℝ) (hFG : Assumptions11 F G)
    (c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ∃ B : ℝ, ∀ n : ℕ, 0 < n → ∀ (φs : ℕ → ℝ) (x : ℝ → ℝ),
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) →
      IsTrajectory (phiForm G) c (stepControl n φs) T x →
      |(∫ t in (0 : ℝ)..T, phiForm F (x t) (stepControl n φs t)) -
          discretePayoff (phiForm F) (phiForm G) c n φs (horizonSteps T n)| ≤ B / n := by sorry

end BellmanDP.Variational
