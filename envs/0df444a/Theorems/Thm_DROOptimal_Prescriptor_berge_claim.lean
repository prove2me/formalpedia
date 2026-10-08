-- Prove2me | Theorems.Thm_DROOptimal_Prescriptor_berge_claim
-- name    : DROOptimal.Prescriptor.berge_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:42.335165+00:00
-- url     : https://prove2.me/theorems/f18b5811-877c-4e5b-8fab-0d8ca7ea562e
-- title:
--   Proof of Theorem 7, p. 21 — for X compact and ĉ continuous, ℙ′ ↦ ĉ(x̂(ℙ′),ℙ′) is continuous for every arg-min selector x̂
-- statement:
--   Let $X\subseteq\mathbb R^n$ be compact, $\mathcal P$ the probability simplex on $\{1,\dots,d\}$, and $\hat c:X\times\mathcal P\to\mathbb R$ a data-driven predictor, i.e. a jointly continuous function. If $\hat x:\mathcal P\to X$ satisfies $\hat x(\mathbb P')\in\arg\min_{x\in X}\hat c(x,\mathbb P')$ for every $\mathbb P'\in\mathcal P$, then the in-sample optimal value
--   $$
--   \mathbb P'\ \mapsto\ \hat c(\hat x(\mathbb P'),\mathbb P')=\min_{x\in X}\hat c(x,\mathbb P')
--   $$
--   is continuous on $\mathcal P$.
--
--   This is the part of Berge's maximum theorem (Berge 1963, pp. 115–116) used in the proof of Theorem 7: it shows that the set where a competing pair is strictly better than the distributionally robust pair is open. No continuity of the selector $\hat x$ itself is required.
--
--   **Formalization Note** The paper's next sentence ("Similarly, $\hat c_r(\hat x_r(\mathbb P'),\mathbb P')$ is continuous") is the instance $\hat c=\hat c_r$, which also needs the continuity of $\hat c_r$ (Proposition 3, a milestone of mission 1 of this series); it is not stated separately.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 21, proof of Theorem 7 (citing Berge 1963, pp. 115–116)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs

namespace DROOptimal.Prescriptor

/-- Proof of Theorem 7, p. 21 (Berge 1963, pp. 115–116): if X is compact, ĉ is a data-driven predictor
and x̂(ℙ′) ∈ arg min_{x ∈ X} ĉ(x, ℙ′) for every ℙ′, then ℙ′ ↦ ĉ(x̂(ℙ′), ℙ′) is continuous on 𝒫. -/
theorem berge_claim {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (hX : IsCompact X)
    (chat : ↥X → DROOptimal.Predictor.Δ d → ℝ) (hchat : DROOptimal.Predictor.IsPredictor chat)
    (xhat : DROOptimal.Predictor.Δ d → ↥X) (hsel : IsArgminSelector chat xhat) :
    Continuous (fun ℙ' : DROOptimal.Predictor.Δ d => chat (xhat ℙ') ℙ') := by sorry

end DROOptimal.Prescriptor
