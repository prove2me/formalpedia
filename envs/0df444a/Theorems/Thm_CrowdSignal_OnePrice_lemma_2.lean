-- Prove2me | Theorems.Thm_CrowdSignal_OnePrice_lemma_2
-- name    : CrowdSignal.OnePrice.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:05.603971+00:00
-- url     : https://prove2.me/theorems/9add7dc9-d8a6-404f-bf8c-bd1d43a1772c
-- title:
--   Lemma 2: unimodal funding profit and optimal prices
-- statement:
--   For either true quality $q_i$ and either believed quality $q_j$, suppose $T<q_j$ and the standing parameter restrictions hold. Write
--   $$p^{ij*}_1=\max\{[4q_j-(1-\alpha)q_i]/8,T\}. $$
--   The expected total profit $\pi^{ij}(p_1)$ is strictly increasing from $T$ to $p^{ij*}_1$ and strictly decreasing from $p^{ij*}_1$ to $q_j$. Its value at $p^{ij*}_1$ is the attained maximum over all funding prices $p_1\ge T$; prices above $q_j$ have zero campaign success probability. The corresponding regular-period price is
--   $$p^{ij*}_2=\begin{cases}q_i/2,&T\le q_j/2,\\Tq_i/q_j,&q_j/2<T<\min\{q_j/[2(1-\alpha)],q_j\},\\q_i/[2(1-\alpha)],&\min\{q_j/[2(1-\alpha)],q_j\}\le T<q_j.\end{cases}$$
--   The stated regular price is feasible and attains the regular-period optimum at $p^{ij*}_1$.
--
--   This result supplies the full-information and low-belief benchmark profits used in the equilibrium analysis.
--
--   **Formalization Note** “Unimodal” is represented by strict monotonicity on the two closed intervals. The theorem is limited to the four quality combinations in the paper and to $T<q_j$; at $T=q_j$ the printed price formula need not be feasible.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 16, Lemma 2

import Mathlib
import Definitions.Def_CrowdSignal_OnePrice_Setting

namespace CrowdSignal.OnePrice

/-- Lemma 2: unimodality, attained funding maximum, and the regular price at it. -/
theorem lemma_2 (P : Params) (hP : P.Standing) (qi qj : ℝ)
    (hi : qi = P.qL ∨ qi = P.qH) (hj : qj = P.qL ∨ qj = P.qH)
    (hT : P.T < qj) :
    let p1s := max ((4 * qj - (1 - P.α) * qi) / 8) P.T
    let p2s := if P.T ≤ qj / 2 then qi / 2
      else if P.T < min (qj / (2 * (1 - P.α))) qj then P.T * qi / qj
      else qi / (2 * (1 - P.α))
    StrictMonoOn (profit P qi qj) (Set.Icc P.T p1s) ∧
    StrictAntiOn (profit P qi qj) (Set.Icc p1s qj) ∧
    IsGreatest (profit P qi qj '' Set.Ici P.T) (profit P qi qj p1s) ∧
    p2s ∈ Set.Ioc (0 : ℝ) qi ∧
    rsProfit P qi qj p1s p2s = rsOpt P qi qj p1s := by sorry

end CrowdSignal.OnePrice
