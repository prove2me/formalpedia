-- Prove2me | Theorems.Thm_FirstOrderOpt_OperatorSliding_gs_convergence_bound
-- name    : FirstOrderOpt.OperatorSliding.gs_convergence_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:06:06.940399+00:00
-- url     : https://prove2.me/theorems/e86de995-fe80-4497-b7ce-ac3ec514a667
-- title:
--   Theorem 8.1(a) — general convergence of the gradient sliding algorithm
-- statement:
--   Continuing `ps_procedure_bound` (Proposition 8.1)'s setting. The gradient sliding (GS)
--   algorithm (Algorithm 8.1) runs, for $k=1,\dots,N$, an outer step computing $x_k = (1-\gamma_k)
--   \bar x_{k-1}+\gamma_kx_{k-1}$, calling $(x_k,\tilde x_k) = \mathrm{PS}(g_k,x_{k-1},\beta_k,T_k)$
--   with $g_k(\cdot) \equiv l_f(x_k,\cdot)$ (8.1.9), then setting $\bar x_k = (1-\gamma_k)\bar
--   x_{k-1}+\gamma_k\tilde x_k$; $\bar x_0=x_0$. An iteration of the PS procedure called at outer
--   step $k$ is an **inner iteration** of the GS algorithm (its own index $t=1,\dots,T_k$, distinct
--   from the outer index $k$). Set
--   $$\Gamma_k := \begin{cases}1,&k=1\\(1-\gamma_k)\Gamma_{k-1},&k\ge2.\end{cases} \quad (8.1.32)$$
--
--   **Theorem 8.1.** Assume $\{p_t\},\{\theta_t\}$ satisfy (8.1.20) and $\{\beta_k\},\{\gamma_k\}$
--   satisfy $\gamma_1=1$, $\beta_k-L\gamma_k\ge0$ for $k\ge1$ (8.1.25). (a) If for any $k\ge2$,
--   $$\frac{\gamma_k\beta_k}{\Gamma_k(1-P_{T_k})} \le
--   \frac{\gamma_{k-1}\beta_{k-1}}{\Gamma_{k-1}(1-P_{T_{k-1}})}, \quad (8.1.33)$$
--   then we have, for any $N\ge1$,
--   $$\Psi(\bar x_N)-\Psi(x^*) \le \mathrm{Bd}(N) := \frac{\Gamma_N\beta_1}{1-P_{T_1}}V(x_0,x^*)
--   + \frac{M^2\Gamma_N}{2}\sum_{k=1}^N\sum_{i=1}^{T_k}\frac{\gamma_kP_{T_k}}
--   {\Gamma_k\beta_k(1-P_{T_k})p_i^2P_{i-1}}, \quad (8.1.34)$$
--   where $x^*\in X$ is an arbitrary optimal solution of (8.1.1), and $P_t,\Gamma_k$ are (8.1.20),
--   (8.1.32).
--
--   **Formalization Note.** `hRecursion` states (8.1.26), the per-outer-step recursion of
--   Proposition 8.2 (cited, not restated — its own proof directly composes `ps_procedure_bound`,
--   the mission's other milestone, with the smooth-model inequalities (8.1.27)-(8.1.31), which are
--   outside this mission's scope). `xIter` is the GS algorithm's own outer iterate sequence
--   (called $x_k$ in the book), kept distinct from the running average `xbar` (called $\bar x_k$):
--   (8.1.26) is stated in terms of Bregman divergences at `xIter`, while the goal quantity is
--   $\Psi(\text{xbar }N)$. Only part (a) (the unbounded-$X$, `hMono` (8.1.33)-monotone case) is
--   formalized; part (b) (compact $X$, the reverse monotonicity) is a further alternative not
--   needed for the goal, `explicit_gs_rate` (Corollary 8.1(a)).
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 491, Theorem 8.1(a)

import Mathlib

namespace FirstOrderOpt.OperatorSliding

/-- Theorem 8.1(a) (general convergence of the outer gradient-sliding, GS, algorithm, unbounded-`X`
case). `Ψ := f+h+chi` on the closed convex `X` (8.1.1). The GS algorithm (Algorithm 8.1) keeps an
"outer" iterate `xIter k` and running average `xbar k` (`xbar 0 = x0`, `xIter 0 = x0`), calling the
PS procedure at each outer step; `hRecursion` is (8.1.26), Proposition 8.2's per-outer-step
recursion (cited, not restated: it is itself proved by combining `ps_procedure_bound`, this
mission's Proposition 8.1, with the model-function inequalities (8.1.27)-(8.1.31)). `P` is (8.1.20)
(cited, not restated) and `Γ` is (8.1.32). `hβγ` is (8.1.25) and `hMono` is (8.1.33), the
unbounded-`X` monotonicity condition part (a) needs. Conclusion: for any `N≥1`, `Ψ(xbar N)-Ψ(x*) ≤
Bd(N)` as in (8.1.34), a sum over outer steps `k=1,…,N` of a further sum over the PS procedure's
own inner steps `i=1,…,T k` called at outer step `k`.

**Formalization Note (revised 2026-09-19).** `hM` tightened to `0 < M` per (8.1.3)'s own "for some
`L>0` and `M>0`". `hTpos` (`T k ≥ 1`) added: without it, `T k = 0` gives `P (T k) = P 0 = 1` (via
`hP0`), so `1 - P (T k) = 0` and `(1 - P (T k))⁻¹ = 0` by Lean's real-division junk convention,
silently zeroing the corresponding term of `hRecursion` and the conclusion at `k=1` — a
zero-length PS call the book's Algorithm 8.1 (p. 488/PDF 498) never contemplates. -/
theorem gs_convergence_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h chi Ψ : E → ℝ) (hΨ : ∀ u, Ψ u = f u + h u + chi u)
    (V : E → E → ℝ) (hVnonneg : ∀ a b, 0 ≤ V a b)
    (L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X)
    (hxstarOpt : ∀ w ∈ X, Ψ xstar ≤ Ψ w)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t) (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (β γ : ℕ → ℝ) (T : ℕ → ℕ) (hTpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ T k)
    (hγ1 : γ 1 = 1) (hβγ : ∀ k : ℕ, 1 ≤ k → 0 ≤ β k - L * γ k)
    (Γ : ℕ → ℝ) (hΓ1 : Γ 1 = 1) (hΓrec : ∀ k : ℕ, 2 ≤ k → Γ k = (1 - γ k) * Γ (k - 1))
    (hMono : ∀ k : ℕ, 2 ≤ k →
      γ k * β k / (Γ k * (1 - P (T k))) ≤ γ (k - 1) * β (k - 1) / (Γ (k - 1) * (1 - P (T (k - 1)))))
    (xIter xbar : ℕ → E) (hxIter0 : xIter 0 = x0) (hxbar0 : xbar 0 = x0)
    (hRecursion : ∀ w ∈ X, ∀ k : ℕ, 1 ≤ k →
      Ψ (xbar k) - Ψ w ≤ (1 - γ k) * (Ψ (xbar (k - 1)) - Ψ w)
        + γ k * (1 - P (T k))⁻¹ *
          (β k * V (xIter (k - 1)) w - β k * V (xIter k) w
            + M ^ 2 * P (T k) / (2 * β k) * ∑ i ∈ Finset.Icc 1 (T k), (p i ^ 2 * P (i - 1))⁻¹))
    (N : ℕ) (hN : 1 ≤ N) :
    Ψ (xbar N) - Ψ xstar ≤
      Γ N * β 1 / (1 - P (T 1)) * V x0 xstar
        + M ^ 2 * Γ N / 2 *
            ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
              γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1)) := by sorry

end FirstOrderOpt.OperatorSliding
