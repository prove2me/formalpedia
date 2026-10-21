-- Prove2me | Theorems.Thm_CoopCluster_EvenSplit_proposition_7_i
-- name    : CoopCluster.EvenSplit.proposition_7_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:26:21.742075+00:00
-- url     : https://prove2.me/theorems/597e38ea-7a77-4f12-9b07-66f46107a39f
-- title:
--   Proposition 7(i), p. 115 (PDF 10) — with t = 0, αO, pO and ΠO decrease in θ
-- statement:
--   Consider the co-opetition game of §4 with an even cost split ($t=0$), under the standing assumptions. Let $0\le\theta_1<\theta_2$, let $(P_1,\alpha_1)$ be a symmetric equilibrium at intensity $\theta_1$ and $(P_2,\alpha_2)$ one at intensity $\theta_2$. Then
--   $$\alpha_2<\alpha_1,\qquad p_2=P_2+\gamma<P_1+\gamma=p_1,\qquad \Pi^O(\theta_2)<\Pi^O(\theta_1),$$
--   where $\Pi^O(\theta_k)=\pi(\alpha_k,P_k,P_k)$ is a provider's equilibrium profit.
--
--   So the equilibrium entertainment level, the equilibrium service fee and the equilibrium profit all fall as price competition intensifies.
--
--   **Formalization Note.** "Decrease" is read as strictly decreasing. Because the statement compares arbitrary equilibria at the two intensities, it does not depend on selecting one equilibrium per $\theta$.
-- source:
--   Yuan, Dai, Chen & Gavirneni, Co-opetition in service clusters with waiting-area entertainment, MSOM 23(1):106–122 (2021), p. 115 (PDF 10), Proposition 7(i)

import Mathlib
import Definitions.Def_CoopCluster_EvenSplit_Model

namespace CoopCluster.EvenSplit

theorem proposition_7_i (M : Params) (hS : M.Standing) (θ₁ θ₂ : ℝ) (h₁ : 0 ≤ θ₁) (h₁₂ : θ₁ < θ₂)
    (P₁ α₁ P₂ α₂ : ℝ) (hE₁ : IsSymEq M θ₁ 0 P₁ α₁) (hE₂ : IsSymEq M θ₂ 0 P₂ α₂) :
    α₂ < α₁ ∧ P₂ + M.γ < P₁ + M.γ ∧
      firmProfit M θ₂ 0 α₂ P₂ P₂ < firmProfit M θ₁ 0 α₁ P₁ P₁ := by sorry

end CoopCluster.EvenSplit
