-- Prove2me | Theorems.Thm_BellmanDP_Variational_euler_error_lemma
-- name    : BellmanDP.Variational.euler_error_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T19:37:25.513339+00:00
-- url     : https://prove2.me/theorems/8c3eb887-3663-462c-a355-b835d6858c47
-- title:
--   Chapter IX, § 12, Lemma (corrected) — the Euler scheme is within $k/n$ of the solution
-- statement:
--   Let $G(x,\varphi)$ be Lipschitz (jointly, with constant $K$) on the strip $m\le x\le M$, $0\le\varphi\le 1$, and let $T\ge 0$. Then there is a constant $\kappa$, depending only on $G$, $T$, $m$, $M$ and $K$, with the following property.
--
--   Let $n\ge 1$, $N=\lfloor Tn\rfloor$, and let $\varphi_0,\dots,\varphi_N\in[0,1]$. Let $\varphi(t)$ be the step function equal to $\varphi_k$ on $k/n\le t<(k+1)/n$, let $x_0=c$, $x_{k+1}=x_k+G(x_k,\varphi_k)/n$, and let $\bar x(t)=x_k$ on $k/n\le t<(k+1)/n$. If $m\le x_k\le M$ for $k=0,\dots,N$, and $x(t)$ is a solution on $[0,T]$ of
--   $$\frac{dx}{dt}=G(x,\varphi(t)),\qquad x(0)=c,$$
--   with $m\le x(t)\le M$, then
--   $$|x(t)-\bar x(t)|\le\frac{\kappa}{n},\qquad 0\le t\le T.$$
--
--   This is the error estimate of Euler's method with a piecewise constant control, and the step that connects the discrete and the continuous problem in the proof of Theorem 2.
--
--   **Formalization Note** Two corrections of the print. The print's range "$0\le t\le N$" is read as the horizon $0\le t\le T$ ($N=\lfloor Tn\rfloor$ steps of length $1/n$). The bounds $m\le x\le M$ are imposed on the solution $x(t)$ as well as on the sequence $x_k$: the print bounds only the sequence, but a Lipschitz condition on the strip says nothing about $G$ outside it, and the proof of Theorem 2 ("Let $m\le x(t)\le M$, and thus $m\le x_k\le M$") supplies both. The constant may depend on $m$, $M$ and the Lipschitz constant, which the Cauchy–Lipschitz argument uses. The solution is in integral form with a continuous $x$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IX, § 12, Lemma, p. 261

import Mathlib
import Definitions.Def_BellmanDP_Variational_Approximation

namespace BellmanDP.Variational

open Set

/-- Bellman, *Dynamic Programming*, Ch. IX, § 12, Lemma, p. 261 (corrected: the print's range
`0 ≤ t ≤ N` is the horizon `0 ≤ t ≤ T`, `N = ⌊T n⌋`; the bounds `m ≤ x ≤ M` are imposed on the
solution `x (t)` as well as on the sequence `x_k`, as in the proof of Theorem 2).
Let `G (x, φ)` be Lipschitz for `m ≤ x ≤ M`, `0 ≤ φ ≤ 1`. There is a constant `κ` depending only
on `G`, `T` (and `m`, `M`) such that for every `n ≥ 1`, every step control with values
`0 ≤ φ_k ≤ 1` on `k/n ≤ t < (k+1)/n`, `k = 0, …, N`, whose Euler states `x_k` (12.6) satisfy
`m ≤ x_k ≤ M`, and every solution `x (t)` of `dx/dt = G (x, φ(t))`, `x (0) = x_0`, staying in
`[m, M]`, we have `|x (t) − x̄ (t)| ≤ κ / n` for `0 ≤ t ≤ T`, where `x̄ (t) = x_k` on
`k/n ≤ t < (k+1)/n`. -/
theorem euler_error_lemma (G : ℝ → ℝ → ℝ) (m M T : ℝ) (K : NNReal) (hT : 0 ≤ T)
    (hG : LipschitzOnWith K (fun z : ℝ × ℝ => G z.1 z.2) (Icc m M ×ˢ Icc (0 : ℝ) 1)) :
    ∃ κ : ℝ, ∀ n : ℕ, 0 < n → ∀ (c : ℝ) (φs : ℕ → ℝ) (x : ℝ → ℝ),
      (∀ k ≤ horizonSteps T n, φs k ∈ Icc (0 : ℝ) 1) →
      (∀ k ≤ horizonSteps T n, eulerTraj G c n φs k ∈ Icc m M) →
      IsTrajectory G c (stepControl n φs) T x →
      (∀ t ∈ Icc 0 T, x t ∈ Icc m M) →
      ∀ t ∈ Icc 0 T, |x t - eulerTraj G c n φs ⌊t * n⌋₊| ≤ κ / n := by sorry

end BellmanDP.Variational
