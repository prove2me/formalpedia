-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_demand_via_T
-- name    : AssortSearch.Cannibal.demand_via_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:24.466539+00:00
-- url     : https://prove2.me/theorems/1324629b-80e8-4cb9-8c27-222928490543
-- title:
--   $q_i^{si}(S)=v_i\,T\big((\sum_{k\in S}v_k+v_0)^{-1}\big)$
-- statement:
--   Let $\mu>0$, let the shocks be i.i.d. zero-mean Gumbel with scale $\mu$, $\bar U=u_r-b$, $\lambda=\exp[-(\bar U/\mu+\gamma)]$ and $T(\omega)=\omega(1-\exp(-\lambda/\omega))$. For $i\in S$, the independent-assortment demand is
--   $$
--   q_i^{si}(S)=v_i\,T\Big(\Big(\sum_{k\in S}v_k+v_0\Big)^{-1}\Big).
--   $$
--   It rewrites Theorem 1 so that the assortment enters only through the total preference $\sum_{k\in S}v_k+v_0$; the paper obtains it "from (3)" in the proof of Theorem 2.
--
--   **Formalization Note** The left-hand side is the probability of the choice event, as in Theorem 1.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 10 (PDF 12), proof of Theorem 2

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- Proof of Theorem 2, p. 10: `q_i^si(S) = v_i T((∑_{k∈S} v_k + v_0)^{-1})`, with
`T` built from `λ = exp[-(Ū/μ + γ)]`. -/
theorem demand_via_T {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) (ur b : ℝ) (w : Fin n → ℝ) (u0 : ℝ) (S : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) :
    searchProb G ur b w u0 S i =
      pref μ w i *
        T (lam μ (searchThreshold ur b)) (∑ k ∈ S, pref μ w k + pref0 μ u0)⁻¹ := by sorry

end AssortSearch.Cannibal
