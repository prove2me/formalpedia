-- Prove2me | Theorems.Thm_BauerleRiederMDP_RegimeSwitching_theorem_4_4_2
-- name    : BauerleRiederMDP.RegimeSwitching.theorem_4_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:59.638852+00:00
-- url     : https://prove2.me/theorems/e1694fd1-07b5-4bb9-88c6-56605c0e292f
-- title:
--   Theorem 4.4.2 — regime switching with power utility: $J_n(x,j)=d_n(j)x^\gamma$ and the optimal policy
-- statement:
--   In the consumption-investment problem with regime switching of §4.4, the environment $(Y_n)$ is an observable Markov chain on a finite set $E_Y$ with transition probabilities $p_{jk}$, the relative risk in environment $j$ is $R(j)$ with law $Q_j$ and $R(j)>-1$ a.s., the interest rate is $i\ge0$ and the discount factor $\beta\in(0,1]$. Assumption (FM) holds: for every $j$ there is no arbitrage ($\varphi\cdot R(j)\ge0$ a.s. implies $\varphi\cdot R(j)=0$ a.s.) and $\mathbb E\|R(j)\|<\infty$. $J_n(x,j)$ denotes the maximal expected discounted utility of consumption and terminal wealth over $n$ periods. Let $U_c(x)=U_p(x)=\frac1\gamma x^\gamma$ on $[0,\infty)$, $0<\gamma<1$, $\delta=(1-\gamma)^{-1}$, and let $v(j)=\sup_{\alpha\in A(j)}\mathbb E(1+\alpha\cdot R(j))^\gamma$ be the value of (4.20). Then:
--
--   1. $J_n(x,j)=d_n(j)x^\gamma$ for $x\ge0$, $j\in E_Y$, where the $d_n(j)>0$ satisfy
--   $$d_0(j)=\gamma^{-1},\qquad d_{n+1}^\delta(j)=\gamma^{-\delta}+\big(\beta(1+i)^\gamma v(j)\big)^\delta\Big(\sum_{k\in E_Y}p_{jk}d_n(k)\Big)^\delta.$$
--   2. Problem (4.20) has an optimal solution $\alpha^*(j)$ for every $j$, and for any such choice and every $N$ the strategy $(f_N^*,\dots,f_1^*)$ with $f_n^*(x,j)=(c_n^*(x,j),a_n^*(x,j))$,
--   $$c_n^*(x,j)=x\big(\gamma d_n(j)\big)^{-\delta},\qquad a_n^*(x,j)=\big(x-c_n^*(x,j)\big)\alpha^*(j),$$
--   is admissible and optimal for the $N$-stage problem.
--
--   Differences from the source:
--   - encoding: value functions as suprema of 𝔼^π over policies in the Markov Decision Model → valueFunction of a DisturbanceMDM: supremum over admissible measurable Markov policies of the EReal expectation under the Ionescu–Tulcea path measure; reason: the book's definition (pp.16–18); Markov policies suffice by Theorem 2.2.3
--   - encoding: state space [0, ∞), next wealth (1 + i)(x − c + a·z) → state space ℝ≥0 with next wealth Real.toNNReal((1 + i)(x − c + a·z)); reason: for admissible actions the wealth is ≥ 0 a.s., so the truncation changes no law; it keeps T inside the state space for every z
--   - reading: α*(j) is the optimal solution of (4.20) → (4.20) has an optimal solution for every j (stated on p.103), and the conclusion holds for every choice of optimal solutions α*(j); reason: with d ≥ 2 redundant assets the optimal solution need not be unique; the book's argument works for each
--   - encoding: the optimal consumption-investment strategy (f*_N, …, f*_1) is defined by f*_n = (c*_n, a*_n) → a Markov policy using f*_{N−k} at time k exists, is admissible, and attains J_N; reason: the book's notion of an optimal policy (p.18)
--   - encoding: the d_n(j) > 0 satisfy the recursion → d_n(j) = dReg M i β γ n j, the positive root, with 0 < d_n(j) asserted; reason: the recursion determines d_{n+1}(j) > 0 uniquely
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.4.2, pp.103–104 (PDF pp.117–118); (4.20), p.103 (PDF p.117)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_J
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_dReg
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- **Theorem 4.4.2** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), pp.103–104, PDF pp.117–118). In the regime-switching model of §4.4
(standing assumptions as in Theorem 4.4.1) with power utilities `U_c(x) = U_p(x) = x^γ / γ`,
`0 < γ < 1`:
a) `J_n(x, j) = d_n(j) x^γ`, `x ≥ 0`, `j ∈ E_Y`, where the `d_n(j) > 0` satisfy `d_0(j) = γ^{-1}`,
`d_{n+1}^δ(j) = γ^{-δ} + (β(1 + i)^γ v(j))^δ (∑_k p_{jk} d_n(k))^δ`, `δ = (1 − γ)^{-1}`, `v(j)` the
value of (4.20);
b) (4.20) has an optimal solution `α*(j)` (p.103), and for any choice of optimal solutions the
strategy `(f*_N, …, f*_1)` with `f*_n(x, j) = (c*_n(x, j), a*_n(x, j))`,
`c*_n(x, j) = x (γ d_n(j))^{-δ}` and `a*_n(x, j) = (x − c*_n(x, j)) α*(j)`, is admissible and
optimal for the `N`-stage problem, for every `N`.

**Formalization Note.** `d_n(j) = dReg M i β γ n j`; the strategy `(f*_N, …, f*_1)` uses
`f*_{N-k}` at time `k`. Optimality: `J^π_N(x, j) = J_N(x, j)` for all `(x, j)` (p.18). -/
theorem theorem_4_4_2 {EY : Type*} [Fintype EY] [MeasurableSpace EY] [DiscreteMeasurableSpace EY]
    {d : ℕ} (M : RegimeMarket EY d) (i : ℝ) (hi : 0 ≤ i) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hR : ∀ j, ∀ᵐ z ∂(M.Q j : Measure (Fin d → ℝ)), ∀ k, -1 < z k)
    (hNA : ∀ j, NoArbitrageLaw (M.Q j : Measure (Fin d → ℝ)))
    (hint : ∀ j, Integrable (fun z : Fin d → ℝ => ∑ k, |z k|) (M.Q j : Measure (Fin d → ℝ)))
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ n (x : ℝ≥0) j, 0 < dReg M i β γ n j ∧
      J M i β (fun c => c ^ γ / γ) (fun c => c ^ γ / γ) n x j =
        ((dReg M i β γ n j * (x : ℝ) ^ γ : ℝ) : EReal)) ∧
    (∀ j, ∃ α ∈ admFrac (M.Q j : Measure (Fin d → ℝ)),
      ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, α k * z k) ^ γ) ∂(M.Q j : Measure (Fin d → ℝ)) =
        powerValue (M.Q j : Measure (Fin d → ℝ)) γ) ∧
    ∀ αstar : EY → Fin d → ℝ, (∀ j, αstar j ∈ admFrac (M.Q j : Measure (Fin d → ℝ)) ∧
        ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, αstar j k * z k) ^ γ) ∂(M.Q j : Measure (Fin d → ℝ)) =
          powerValue (M.Q j : Measure (Fin d → ℝ)) γ) →
      ∀ N, ∃ π : MarkovPolicy (ℝ≥0 × EY) (ℝ × (Fin d → ℝ)),
        (∀ k < N, ∀ (x : ℝ≥0) j, π.f k (x, j) =
          ((x : ℝ) * (γ * dReg M i β γ (N - k) j) ^ (-(1 - γ)⁻¹),
            fun l => ((x : ℝ) - (x : ℝ) * (γ * dReg M i β γ (N - k) j) ^ (-(1 - γ)⁻¹)) *
              αstar j l)) ∧
        π.IsAdmissible (regimeModel M i β (fun c => c ^ γ / γ)) 0 N ∧
        ∀ (x : ℝ≥0) j, policyValue (regimeModel M i β (fun c => c ^ γ / γ))
            (fun s => β ^ N * ((s.1 : ℝ) ^ γ / γ)) N π 0 (x, j) =
          J M i β (fun c => c ^ γ / γ) (fun c => c ^ γ / γ) N x j := by sorry

end BauerleRiederMDP.RegimeSwitching
