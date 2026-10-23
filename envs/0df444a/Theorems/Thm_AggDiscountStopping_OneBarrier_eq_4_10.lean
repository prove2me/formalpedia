-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_eq_4_10
-- name    : AggDiscountStopping.OneBarrier.eq_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:13.3429+00:00
-- url     : https://prove2.me/theorems/7e9d05b5-e872-4dec-9428-53f08eb8f115
-- title:
--   (4.10), p. 18 — for a* ≤ a < b ≤ min(x, K), J(x, [0, b]) < J(x, [0, a]); with b = x this is ϕ(g(x)) < Λ(x, a)
-- statement:
--   Assume the hypotheses of Theorem 4.8 (standing assumptions, Conditions C-(i)–C-(iii) with a fixed $\epsilon>0$, a diffusion with continuous non-negative paths, the Laplace representation, and integrability of $r\mapsto\varphi_r'(a)/\varphi_r(a)$ for each $a>0$). Let $a^*\in[0,K)$ be such that, for every $a\in(0,K)$, $G(a)+\frac1{K-a}>0$ if and only if $a>a^*$ (the characterization (4.9)). Then for all $a,b,x$ with
--   $$0<a,\quad a^*\le a<b\le x,\quad b\le K,$$
--   we have
--   $$J(x,[0,b])<J(x,[0,a]).$$
--
--   With $b=x$ this is the first inequality of (4.10), $\phi(g(x))=\Lambda(x,x)<\Lambda(x,a)$: above an admissible barrier, continuing is strictly better than stopping. Comparing two barriers is the second inequality, $\Lambda(x,a)<\Lambda(x,a^*)$: the value decreases strictly as the barrier is raised above $a^*$.
--
--   **Formalization Note** $\Lambda(x,a)=J(x,(0,a])$ is replaced by $J(x,[0,a])$ (equal for $x\ge a$). The comparison is stated for every pair $a^*\le a<b$ with $a>0$, which avoids evaluating a barrier at $a^*=0$, where $\varphi_r(0)$ may be infinite.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, proof of Theorem 4.8, (4.10), p. 18

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem eq_4_10 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (hCi : M.CondI) (hCii1 : M.CondII1) (ε : ℝ) (hε : 0 < ε) (hCii2 : M.CondII2 ε)
    (hCiii : M.CondIII) (D : Diffusion Ω) (hD : D.Valid) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ)
    (hG : ∀ a, 0 < a → Integrable (fun r => deriv (φ r) a / φ r a) M.F)
    (aStar : ℝ) (haStar0 : 0 ≤ aStar) (haStarK : aStar < M.K)
    (haStar : ∀ a ∈ Ioo 0 M.K, (0 < G M φ a + 1 / (M.K - a) ↔ aStar < a)) :
    ∀ a b x, 0 < a → aStar ≤ a → a < b → b ≤ x → b ≤ M.K →
      J M D x (Icc 0 b) < J M D x (Icc 0 a) := by sorry

end AggDiscountStopping.OneBarrier
