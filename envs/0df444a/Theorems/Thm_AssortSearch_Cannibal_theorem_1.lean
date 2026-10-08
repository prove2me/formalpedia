-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_theorem_1
-- name    : AssortSearch.Cannibal.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:57.06641+00:00
-- url     : https://prove2.me/theorems/7a146ede-4243-4c11-83ff-974afb233e7f
-- title:
--   Theorem 1 — independent-assortment demand $q_i^{si}(S)=q_i^m(S)\,(1-H(\bar U,S))$
-- statement:
--   Let $\mu>0$ and let the consumer's shocks be i.i.d. zero-mean Gumbel with scale $\mu$. In the independent assortment search model a consumer who finds $U_{\max}>U_0$ either buys her most preferred variant or searches at cost $b$ for an outside utility $U_r=u_r+\zeta_r$, choosing whichever her search rule prescribes. Then the demand for variant $i$ is
--   $$
--   q_i^{si}(S)=q_i^m(S)\,\big(1-H(\bar U,S)\big),\qquad i\in S,
--   $$
--   where $q_i^m(S)=v_i/(\sum_{j\in S}v_j+v_0)$, $\bar U=u_r-b$, $H(\bar U,S)=\exp\big(-\lambda(v_0+\sum_{j\in S}v_j)\big)$ and $\lambda=\exp[-(\bar U/\mu+\gamma)]$.
--
--   Search scales every variant's no-search demand by the same factor $1-H(\bar U,S)$, the probability that the best option in the store beats the search threshold. The threshold $\bar U$ does not depend on the assortment.
--
--   **Formalization Note** The left-hand side is the probability of the choice event of the random-utility model, not the closed form; $q_i^m(S)$ on the right is the published `RetailVariety.Structure.share` evaluated at the preferences.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 8 (PDF 10), Theorem 1, equation (3)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- **Theorem 1**, p. 8: in the independent assortment search model,
`q_i^si(S) = q_i^m(S) (1 - H(Ū, S))` for `i ∈ S`, where `Ū = u_r - b`,
`H(Ū, S) = exp(-λ(v_0 + ∑_{j∈S} v_j))` and `λ = exp[-(Ū/μ + γ)]`. -/
theorem theorem_1 {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) (ur b : ℝ) (w : Fin n → ℝ) (u0 : ℝ) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) :
    searchProb G ur b w u0 S i =
      RetailVariety.Structure.share (pref μ w) (pref0 μ u0) S i *
        (1 - H μ (searchThreshold ur b) (pref μ w) (pref0 μ u0) S) := by sorry

end AssortSearch.Cannibal
