-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_eq_37
-- name    : EpiControl.SinglePeak.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:36.686557+00:00
-- url     : https://prove2.me/theorems/a18660bc-4afd-4afc-b13d-0ffb3966cf7d
-- title:
--   (37), p. 24 (PDF 25) — under Assumption 1, the second-derivative bound on the gain g∗
-- statement:
--   Suppose Assumption 1 holds with $c'(\bar b-)$ the left derivative of $c$ at $\bar b$. Let $\beta^*$ be an optimal policy with SIR path $(s^*,i^*)$ and costate $\eta^*$ as in Proposition 1, let $g^*=\eta^*i^*s^*$, and suppose $\beta^*(t)\in\arg\min_{b\in B}[g^*(t)b+c(b)]$ for every $t\in[0,T]$ (the convention of p. 7). Let
--   $$G(t)=-\gamma g^*(t)+s^*(t)\Big(M(g^*(t))-M(g^*(T))-\big[v'(i^*(t))i^*(t)-v(i^*(t))\big]\Big)$$
--   be the right-hand side of (7), so $G=(g^*)'$ on $[0,T]$. Then for almost every $t\in[0,T]$, $G$ is differentiable at $t$ and
--   $$(g^*)''(t)\le\Big[-\gamma+\beta^*(t)\big(s^*(t)-i^*(t)\big)-\frac{v''(i^*(t))\,i^*(t)^2s^*(t)}{g^*(t)}\Big](g^*)'(t)-g^*(t)\beta^*(t)i^*(t)\Big[\frac{4v''(i^*(t))}{27\,c'(\bar b-)}\Big(\frac{\bar b}{\underline b}-1\Big)+\gamma\Big]. \tag{37}$$
--
--   This differential inequality is what forces every critical point of $g^*$ in $(0,T)$ to be a strict local maximum.
--
--   **Formalization Note** $(g^*)'$ is written as $G$ and $(g^*)''$ as the derivative of $G$. Assumption 1 forces $c'(\bar b-)\neq 0$ (footnote 19: otherwise $v''<0$, contradicting convexity), so the division by $27c'(\bar b-)$ is genuine; $g^*>0$ makes the division by $g^*(t)$ genuine.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 24 (PDF 25), proof of Proposition 7, (37)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem eq_37 (P : Params) (hP : P.Standing) (dc : ℝ) (hA1 : P.Assumption1 dc)
    (β s i : ℝ → ℝ) (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η)
    (hconv : ∀ t ∈ Icc 0 P.T, P.ArgminAt (gain η s i t) (β t)) :
    let g : ℝ → ℝ := gain η s i
    let G1 : ℝ → ℝ := fun t =>
      -P.γ * g t + s t * (P.M (g t) - P.M (g P.T) - (deriv P.v (i t) * i t - P.v (i t)))
    ∀ᵐ t ∂(volume.restrict (Icc 0 P.T)),
      DifferentiableAt ℝ G1 t ∧
      deriv G1 t ≤
        (-P.γ + β t * (s t - i t) - deriv (deriv P.v) (i t) * i t ^ 2 * s t / g t) * G1 t -
          g t * β t * i t *
            (4 * deriv (deriv P.v) (i t) / (27 * dc) * (P.bbar / P.bl - 1) + P.γ) := by sorry
end EpiControl.SinglePeak
