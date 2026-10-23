-- Prove2me | Theorems.Thm_CrowdSignal_TwoPrice_lemma_4
-- name    : CrowdSignal.TwoPrice.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:11.166989+00:00
-- url     : https://prove2.me/theorems/aeaf75eb-2d3b-4136-8d73-8d5460afb36a
-- title:
--   Lemma 4, p. 23 — optimal committed funding and regular prices
-- statement:
--   Let an entrepreneur have true quality $q_i$ and be believed to have quality $q_j$, with $i,j\in\{L,H\}$. Assume $0<T\le q_j$ and the standing quality and customer-share conditions. His expected two-period payoff is $\Pi^{ij}(P_1,P_2)$, maximized over $P_1\ge T$ and $P_2>0$. Set
--   $$P_1^{ij*}=\max\left\{\frac{4q_j-(1-\alpha)q_i}{8},T\right\},\qquad P_2^{ij*}=\begin{cases}q_i/2,&T\le q_j/2,\\Tq_i/q_j,&q_j/2<T<q_j/[2(1-\alpha)],\\q_i/[2(1-\alpha)],&q_j/[2(1-\alpha)]\le T\le q_j.\end{cases}$$
--   The pair $(P_1^{ij*},P_2^{ij*})$ is feasible and attains the maximum of $\Pi^{ij}$ over all feasible pairs.
--
--   This result supplies the full-information low- and high-type prices and the reference payoffs used in the separating-equilibrium analysis.
--
--   **Formalization Note** The bound $T\le q_j$ records the printed domain of (11); outside it no funding price can yield a positive success probability. The result asserts attainment, without adding uniqueness.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 23, Lemma 4 and (11)

import Mathlib
import Definitions.Def_CrowdSignal_TwoPrice_Setting

namespace CrowdSignal.TwoPrice

/-- Lemma 4, p. 23, equation (11). -/
theorem lemma_4 (P : Params) (hP : P.Standing) (qi qj : ℝ)
    (hi : qi = P.qL ∨ qi = P.qH) (hj : qj = P.qL ∨ qj = P.qH)
    (hTj : P.T ≤ qj) :
    let P1s := max ((4 * qj - (1 - P.α) * qi) / 8) P.T
    let P2s := if P.T ≤ qj / 2 then qi / 2
      else if P.T < qj / (2 * (1 - P.α)) then P.T * qi / qj
      else qi / (2 * (1 - P.α))
    Feas P (P1s, P2s) ∧
      IsGreatest (payoff P qi qj '' {x | Feas P x}) (payoff P qi qj (P1s, P2s)) := by sorry

end CrowdSignal.TwoPrice
