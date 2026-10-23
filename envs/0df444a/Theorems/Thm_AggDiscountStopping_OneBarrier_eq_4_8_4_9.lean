-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_eq_4_8_4_9
-- name    : AggDiscountStopping.OneBarrier.eq_4_8_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:08.384679+00:00
-- url     : https://prove2.me/theorems/113e09b7-5f69-40a9-a598-8fc67eb4e521
-- title:
--   (4.8)–(4.9), p. 17 — G(a) + 1/(K − a) is strictly increasing and continuous on (0, K), and G(a) > −1/(K − a) iff a > a*
-- statement:
--   Assume the standing assumptions and Conditions C-(i) and C-(ii)-1. Let $(\varphi_r)_{r\ge0}$ be positive, decreasing, $C^2$ solutions on $(0,\infty)$ of (4.1), with $r\mapsto\varphi_r'(a)/\varphi_r(a)$ integrable against $F_\rho$ for every $a>0$, and let
--   $$G(a)=\int_0^\infty\frac{\varphi_r'(a)}{\varphi_r(a)}dF_\rho(r).\qquad(4.8)$$
--   Then the function $h(a)=G(a)+\frac1{K-a}$ satisfies:
--   1. $h$ is strictly increasing and continuous on $(0,K)$;
--   2. $h(a)>0$ for all $a<K$ close enough to $K$;
--   3. there is $a^*\in[0,K)$ such that $h(a^*)=0$ if $a^*>0$, and for every $a\in(0,K)$,
--   $$G(a)>-\frac1{K-a}\iff a>a^*.\qquad(4.9)$$
--
--   The number $a^*$ is the threshold of Theorem 4.8. It depends only on the process and on $F_\rho$, not on the attitude function (Remark 4.9).
--
--   **Formalization Note** The printed "$a^*=0$ if $G(a)+1/(K-a)>0$ for all $a\in[0,K)$" is read on $(0,K)$, because $G(0)$ involves $\varphi_r(0)$, which may be infinite. "$\lim_{a\to K}G(a)+\frac1{K-a}>0$" is posed as eventual positivity to the left of $K$. The integrability of $G$'s integrand is the paper's implicit finiteness of $G$. Conditions C-(ii)-2 and C-(iii) of the theorem are not needed for this step and are not assumed.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, proof of Theorem 4.8, (4.8)–(4.9), p. 17

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem eq_4_8_4_9 (M : Model) (hM : M.Valid) (hCi : M.CondI) (hCii1 : M.CondII1)
    (φ : ℝ → ℝ → ℝ) (hφ : ∀ r, 0 ≤ r → IsDecreasingSolution M r (φ r))
    (hG : ∀ a, 0 < a → Integrable (fun r => deriv (φ r) a / φ r a) M.F) :
    StrictMonoOn (fun a => G M φ a + 1 / (M.K - a)) (Ioo 0 M.K) ∧
      ContinuousOn (fun a => G M φ a + 1 / (M.K - a)) (Ioo 0 M.K) ∧
      (∀ᶠ a in 𝓝[<] M.K, 0 < G M φ a + 1 / (M.K - a)) ∧
      ∃ aStar : ℝ, 0 ≤ aStar ∧ aStar < M.K ∧
        (0 < aStar → G M φ aStar + 1 / (M.K - aStar) = 0) ∧
        ∀ a ∈ Ioo 0 M.K, (0 < G M φ a + 1 / (M.K - a) ↔ aStar < a) := by sorry

end AggDiscountStopping.OneBarrier
