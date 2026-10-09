-- Prove2me | Theorems.Thm_DynAssortPers_Regret_lemma_choice_prob_lipschitz
-- name    : DynAssortPers.Regret.lemma_choice_prob_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:52.373384+00:00
-- url     : https://prove2.me/theorems/a2479293-e562-4cfd-8b32-ef44598c4572
-- title:
--   p. 47 — $|p_j(S;\theta)-p_j(S;\theta')|\le\frac14\sqrt{|S|}\,\|\theta-\theta'\|_2$
-- statement:
--   Let $S\subseteq\{1,\dots,n\}$ be an assortment, $j\in S$, and $\theta,\theta'\in\mathbb R^n$. The MNL choice probability $p_j(S;\theta)=e^{\theta_j}/(1+\sum_{j'\in S}e^{\theta_{j'}})$ is Lipschitz in the parameters:
--   $$|p_j(S;\theta)-p_j(S;\theta')|\le\frac14\sqrt{|S|}\,\|\theta-\theta'\|_2 .$$
--
--   This is the first step of the proof of Theorem 6: it makes the expected revenue of a fixed assortment continuous in the estimated parameters.
--
--   **Formalization Note** $\|\theta-\theta'\|_2=\sqrt{\sum_j(\theta_j-\theta'_j)^2}$. The bound is stated for $p_j$ with the term $1+$ in the denominator (p. 21); the derivative display on p. 47 omits it, and the constant $\frac14$ holds for the definition with it.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), proof of Theorem 6, p. 47, display after 'This means that for any S, j ∈ S, θ, and θ′'

import Mathlib
import Definitions.Def_DynAssortPers_Regret_MNL

namespace DynAssortPers.Regret

/-- Proof of Theorem 6, p. 47: for any `S`, `j ∈ S`, `θ`, `θ'`,
`|p_j(S; θ) − p_j(S; θ')| ≤ (1/4) √|S| ‖θ − θ'‖₂`. -/
theorem lemma_choice_prob_lipschitz {n : ℕ} (S : Finset (Fin n)) (j : Fin n) (hj : j ∈ S)
    (θ θ' : Fin n → ℝ) :
    |choiceProb θ S j - choiceProb θ' S j| ≤
      (1 / 4) * Real.sqrt (S.card : ℝ) * euclidDist θ θ' := by sorry

end DynAssortPers.Regret
