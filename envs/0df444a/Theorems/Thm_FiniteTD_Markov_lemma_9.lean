-- Prove2me | Theorems.Thm_FiniteTD_Markov_lemma_9
-- name    : FiniteTD.Markov.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:29.216983+00:00
-- url     : https://prove2.me/theorems/d7ef8be0-7e01-488d-9b78-385df4961e99
-- title:
--   Lemma 9, p. 20 — control of coupling: |E v(X,Y) − E v(X′,Y′)| ≤ 2‖v‖∞ mρ^τ
-- statement:
--   Let $P$ be a stochastic matrix on a finite set $S$ with stationary distribution $\pi$, satisfying Assumption 1 with constants $m>0$, $\rho\in(0,1)$. Fix $t\in\mathbb{N}_0$ and $\tau>0$. Let $X$ and $Y$ be random variables on measurable spaces such that $X\to s_t\to s_{t+\tau}\to Y$ is a Markov chain. Let $X',Y'$ be independent with the marginal laws of $X$ and $Y$. Then for every measurable function $v$ with $|v|\le V$,
--   $$\big|\mathbb{E}[v(X,Y)]-\mathbb{E}[v(X',Y')]\big|\;\le\;2V\,m\rho^{\tau}.$$
--
--   This is the information-theoretic estimate that decouples the iterate $\theta_{t-\tau}$ from the observation $O_t$ in the proof of Lemma 11.
--
--   **Formalization Note** The probability measures $K_X(s)$ and $K_Y(u)$ encode the conditional laws of $X$ given $s_t=s$ and of $Y$ given $s_{t+\tau}=u$. Stationarity gives the middle pair law $\pi(s)P^\tau(s,u)$. The first sum of iterated integrals is $\mathbb{E}[v(X,Y)]$ and the second is $\mathbb{E}[v(X',Y')]$. Measurability is implicit in the paper's expectations; boundedness then gives integrability under these probability laws. The bound for every $V\ge\sup|v|$ is equivalent to the paper's bound with $\|v\|_\infty$.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 20, Lemma 9

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain

namespace FiniteTD.Markov

/-- `KX s` and `KY u` are the conditional laws of `X` given `s_t = s` and
`Y` given `s_{t+τ} = u`. Their
factorization with `π(s) P^τ(s,u)` is exactly `X → s_t → s_{t+τ} → Y`. -/
theorem lemma_9 {S A B : Type} [Fintype S] [DecidableEq S]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : S → S → ℝ) (π : S → ℝ) (m ρ : ℝ)
    (hP : IsStochastic P) (hπ : IsStationaryDist P π) (hA1 : Assumption1 P π m ρ)
    (t τ : ℕ) (hτ : 0 < τ)
    (KX : S → MeasureTheory.Measure A) (KY : S → MeasureTheory.Measure B)
    (hKX : ∀ s, MeasureTheory.IsProbabilityMeasure (KX s))
    (hKY : ∀ u, MeasureTheory.IsProbabilityMeasure (KY u))
    (v : A → B → ℝ) (V : ℝ)
    (hvm : Measurable (fun p : A × B => v p.1 p.2))
    (hv : ∀ a b, |v a b| ≤ V) :
    |(∑ s : S, ∑ u : S, π s * (Matrix.of P ^ τ) s u *
        (∫ a, (∫ b, v a b ∂(KY u)) ∂(KX s))) -
      (∑ s : S, ∑ u : S, π s * π u *
        (∫ a, (∫ b, v a b ∂(KY u)) ∂(KX s)))|
      ≤ 2 * V * (m * ρ ^ τ) := by sorry

end FiniteTD.Markov
