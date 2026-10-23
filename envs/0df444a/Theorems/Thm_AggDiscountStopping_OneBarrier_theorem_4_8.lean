-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_theorem_4_8
-- name    : AggDiscountStopping.OneBarrier.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:05.069875+00:00
-- url     : https://prove2.me/theorems/832b30b5-7903-4340-abfb-372cbc4f413e
-- title:
--   Theorem 4.8, p. 16 (optimality among one-barrier equilibria) — [0, a] is an equilibrium iff a ≥ a*, and [0, a*] is optimal
-- statement:
--   Consider the time-inconsistent stopping problem with Put payoff $g(x)=(K-x)^+$, diffusion state $X$, random discount rate with law $F_\rho$ on $[0,\infty)$ and attitude function $\phi$, with aggregated payoff
--   $$J(x,R)=\int_0^\infty\phi\Big(\mathbb E\big[e^{-r\tau(x,R)}g(X^x_{\tau(x,R)})\big]\Big)dF_\rho(r),$$
--   equilibria $R=\Theta(R)$ and value $V(x,R)=\phi(g(x))\vee J(x,R)$. Assume Conditions C-(i), C-(ii) (with a fixed $\epsilon>0$) and C-(iii), the hitting-time Laplace representation $\mathbb E[e^{-r\tau^x_a}]=\varphi_r(x)/\varphi_r(a)$ of Remark 4.3, and that $G(a)=\int_0^\infty\varphi_r'(a)/\varphi_r(a)\,dF_\rho(r)$ is finite for every $a>0$. Then there is a threshold $a^*$ with $0\le a^*<K$ such that:
--   1. for every $a>0$, the one-barrier region $[0,a]$ is an equilibrium if and only if $a\ge a^*$;
--   2. for $a^*\le a\le b$ with $a>0$, the value decreases as the barrier rises:
--   $$V(x,[0,b])\le V(x,[0,a])\qquad\text{for all }x\ge0;$$
--   3. if $a^*>0$, the smallest one-barrier equilibrium $[0,a^*]$ is optimal among one-barrier equilibria: $V(x,[0,a^*])\ge V(x,[0,b])$ for every $x\ge0$ and every equilibrium $[0,b]$, $b>0$.
--
--   This is the paper's main result on one-barrier equilibria: the smallest one is the best for every initial state.
--
--   **Formalization Note** The paper's Theorem 4.8 calls $[0,a^*]$ "the optimal equilibrium" in the sense of Definition 4.1 (dominance over every equilibrium), but its proof compares $[0,a^*]$ only with regions $[0,a]$; the statement poses optimality among one-barrier equilibria and neither the all-equilibria version nor its negation. Barriers are $a>0$, since for geometric Brownian motion or Bessel processes $0$ is never hit and $\varphi_r(0)=+\infty$; when $a^*=0$ the content is item 2. The bound $a^*<K$ is the proof's root $\hat a\in[0,K)$. The process is encoded by continuous non-negative paths and the Laplace representation (see the Setting module); finiteness of $G$ is the paper's implicit assumption. Every hypothesis of the theorem is satisfiable (for example by geometric Brownian motion with $\mu=\sigma=1$, Example-1), and the conclusion is not vacuous: equilibria require a Borel fixed point of $\Theta$ with the strict entry time.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, Theorem 4.8, p. 16 (proof pp. 17–18)

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem theorem_4_8 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (hCi : M.CondI) (hCii1 : M.CondII1) (ε : ℝ) (hε : 0 < ε) (hCii2 : M.CondII2 ε)
    (hCiii : M.CondIII) (D : Diffusion Ω) (hD : D.Valid) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ)
    (hG : ∀ a, 0 < a → Integrable (fun r => deriv (φ r) a / φ r a) M.F) :
    ∃ aStar : ℝ, 0 ≤ aStar ∧ aStar < M.K ∧
      (∀ a, 0 < a → (IsEquilibrium M D (Icc 0 a) ↔ aStar ≤ a)) ∧
      (∀ a b, 0 < a → aStar ≤ a → a ≤ b → ∀ x, 0 ≤ x →
        Vval M D x (Icc 0 b) ≤ Vval M D x (Icc 0 a)) ∧
      (0 < aStar → IsOptimalOneBarrier M D aStar) := by sorry

end AggDiscountStopping.OneBarrier
