-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_proposition_4_2
-- name    : AggDiscountStopping.OneBarrier.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:10.282022+00:00
-- url     : https://prove2.me/theorems/9afc4673-b5f0-42aa-9d7e-f54c5f4993be
-- title:
--   Proposition 4.2, pp. 10–11 — H(r, a, x) = ln E[e^{−rτ^x_a}]: (a) right x-derivative at the barrier increasing in a; (b) ∂_aH increasing in r
-- statement:
--   Assume the standing assumptions, Conditions C-(i), C-(ii)-1 and C-(ii)-2 (for a fixed $\epsilon>0$), a diffusion with continuous non-negative paths, and the Laplace representation $\mathbb E[e^{-r\tau^x_a}]=\varphi_r(x)/\varphi_r(a)$ of Remark 4.3. Let
--   $$H(r,a,x)=\ln\mathbb E\big[e^{-r\tau^x_a}\big],\qquad \tau^x_a=\inf\{t>0:X^x_t=a\}.$$
--   Then:
--   1. for every $r\ge0$, the right derivative $\lim_{x\downarrow a}\partial_xH(r,a,x)$, i.e. the derivative of $x\mapsto H(r,a,x)$ at $x=a$ within $[a,\infty)$, is increasing in $a\in(0,K]$;
--   2. for every $0<a<x$, $\partial_aH(r,a,x)$ is increasing in $r\in[0,\infty)$.
--
--   These two monotonicity properties of the hitting-time Laplace transform are the conditions under which the smallest one-barrier equilibrium is optimal.
--
--   **Formalization Note** "$\lim_{x\downarrow a}\partial_xH$" is the one-sided derivative within $[a,\infty)$; the two agree because $H(r,a,\cdot)=\ln\varphi_r(\cdot)-\ln\varphi_r(a)$ is $C^1$ on $(0,\infty)$. Barriers are $a>0$ (printed $a\in[0,K]$), since $\tau^x_0$ may be infinite almost surely (geometric Brownian motion, Bessel process). Part (b) is posed for $a<x$ (printed $a\le x$): the derivative in $a$ at $a=x$ involves barriers above the starting point, where the Laplace representation says nothing. C-(i) is the standing condition of §4.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, Proposition 4.2, pp. 10–11

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem proposition_4_2 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (hCi : M.CondI) (hCii1 : M.CondII1) (ε : ℝ) (hε : 0 < ε) (hCii2 : M.CondII2 ε)
    (D : Diffusion Ω) (hD : D.Valid) (φ : ℝ → ℝ → ℝ) (hφ : IsLaplaceRep M D φ) :
    (∀ r, 0 ≤ r →
        MonotoneOn (fun a => derivWithin (fun x => D.H r a x) (Ici a) a) (Ioc 0 M.K)) ∧
      (∀ a x, 0 < a → a < x →
        MonotoneOn (fun r => deriv (fun b => D.H r b x) a) (Ici 0)) := by sorry

end AggDiscountStopping.OneBarrier
