-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_eq_2
-- name    : AssortSearch.Cannibal.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:01.387283+00:00
-- url     : https://prove2.me/theorems/7ad53990-694d-40bc-905a-8d1eee64f53f
-- title:
--   (2) — MNL choice probabilities $q_i^m(S)=v_i/(\sum_{j\in S}v_j+v_0)$ under zero-mean Gumbel shocks
-- statement:
--   Let $\mu>0$ and let the shocks $\zeta_0,\zeta_1,\dots,\zeta_n$ be i.i.d. with the zero-mean Gumbel law of scale $\mu$. Write $v_j=\exp((u_j-p_j)/\mu)$ and $v_0=\exp(u_0/\mu)$. In the traditional no-search model a consumer buys the variant of $S$ with the highest utility, or nothing if the no-purchase utility $U_0$ is higher. Then, for every assortment $S$,
--   $$
--   q_i^m(S)=\frac{v_i}{\sum_{j\in S}v_j+v_0}\qquad\text{for } i=0 \text{ and } i\in S .
--   $$
--   This is the multinomial logit formula, which the paper cites as well known (Anderson, de Palma and Thisse 1992, Chapter 2). It is the no-search benchmark against which the search models are compared.
--
--   **Formalization Note** The case $i=0$ is the probability that $U_0$ exceeds every $U_j$, $j\in S$. For $i\in S$ the right-hand side is the published `RetailVariety.Structure.share`.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 7 (PDF 9), equation (2)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- **(2)**, p. 7: the MNL formula. Under i.i.d. zero-mean Gumbel shocks with scale `μ`, the
no-search choice probabilities are `q_0^m(S) = v_0/(∑_{j∈S} v_j + v_0)` and
`q_i^m(S) = v_i/(∑_{j∈S} v_j + v_0)` for `i ∈ S`. -/
theorem eq_2 {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) (w : Fin n → ℝ) (u0 : ℝ) (S : Finset (Fin n)) :
    noSearchProb G w u0 S none = pref0 μ u0 / (∑ j ∈ S, pref μ w j + pref0 μ u0) ∧
    ∀ i ∈ S, noSearchProb G w u0 S (some i) =
      RetailVariety.Structure.share (pref μ w) (pref0 μ u0) S i := by sorry

end AssortSearch.Cannibal
