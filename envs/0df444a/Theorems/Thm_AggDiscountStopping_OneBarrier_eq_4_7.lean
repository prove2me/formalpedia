-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_eq_4_7
-- name    : AggDiscountStopping.OneBarrier.eq_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:17.04899+00:00
-- url     : https://prove2.me/theorems/8ccb4c2d-d9d3-4761-9745-bc793bfbc9b2
-- title:
--   (4.7), p. 17 — the right x-derivative of J(x, [0, a]) at x = a equals ϕ′(K − a)(K − a)G(a)
-- statement:
--   Assume the hypotheses of Theorem 4.8: the standing assumptions, Conditions C-(i)–C-(iii) (with a fixed $\epsilon>0$), a diffusion with continuous non-negative paths and the Laplace representation $\mathbb E[e^{-r\tau^x_a}]=\varphi_r(x)/\varphi_r(a)$, and integrability of $r\mapsto\varphi_r'(a)/\varphi_r(a)$ against $F_\rho$ for each $a>0$. Let $0<a<K$ and $G(a)=\int_0^\infty\varphi_r'(a)/\varphi_r(a)\,dF_\rho(r)$. Then $x\mapsto J(x,[0,a])$ has a right derivative at $x=a$, and
--   $$\lim_{x\downarrow a}\frac{\partial J(x,[0,a])}{\partial x}=\phi'(K-a)\,(K-a)\,G(a).$$
--
--   Comparing this with the derivative $-\phi'(K-a)$ of $x\mapsto\phi(g(x))$ decides whether points just above the barrier prefer to stop, which is how barriers below the threshold $a^*$ are excluded.
--
--   **Formalization Note** The paper writes $\Lambda(x,a)=J(x,(0,a])$; the statement uses $J(x,[0,a])$, which equals it for $x>a$ and at $x=a$ (both are $\phi(K-a)$). The right partial derivative is the derivative within $[a,\infty)$ (`HasDerivWithinAt … (Ici a) a`), which exists and equals the printed limit; $\lim_{x\downarrow a}\partial_xH(r,a,x)=\varphi_r'(a)/\varphi_r(a)$ by Remark 4.3. The integrability of $G$'s integrand is the paper's implicit finiteness of $G$ ("$G$ … is clearly continuous").
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, proof of Theorem 4.8, (4.5)–(4.7), p. 17

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem eq_4_7 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (hCi : M.CondI) (hCii1 : M.CondII1) (ε : ℝ) (hε : 0 < ε) (hCii2 : M.CondII2 ε)
    (hCiii : M.CondIII) (D : Diffusion Ω) (hD : D.Valid) (φ : ℝ → ℝ → ℝ)
    (hφ : IsLaplaceRep M D φ)
    (hG : ∀ a, 0 < a → Integrable (fun r => deriv (φ r) a / φ r a) M.F)
    (a : ℝ) (ha : 0 < a) (haK : a < M.K) :
    HasDerivWithinAt (fun x => J M D x (Icc 0 a))
      (deriv M.att (M.K - a) * (M.K - a) * G M φ a) (Ici a) a := by sorry

end AggDiscountStopping.OneBarrier
