-- Prove2me | Theorems.Thm_CrowdSignal_TwoPrice_proposition_2
-- name    : CrowdSignal.TwoPrice.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:15.160159+00:00
-- url     : https://prove2.me/theorems/049d78aa-3d33-4235-b03c-4c006b2c5a81
-- title:
--   Proposition 2, pp. 26–27 — unique refined separating equilibrium under price commitment
-- statement:
--   Let $0<q_L<q_H\le(\alpha^2+6\alpha+25)q_L/16$, $0<\alpha<1$, and $0<T\le(3+\alpha)q_L/8$. Let $(\dot P_1,\dot P_2)$ solve $4\dot P_1+(1-\alpha)\dot P_2=2q_H$ and $W^{LH}(\dot P_1,\dot P_2)=\Pi^{L*}$, with $\dot P_2>q_H/2$ and $T\le\dot P_1$. Then a separating equilibrium surviving the intuitive criterion exists with the high type charging $(\dot P_1,\dot P_2)$ and the low type charging $((3+\alpha)q_L/8,q_L/2)$.
--
--   Every separating equilibrium surviving the intuitive criterion has exactly these two pairs, and the low type's pair attains his full-information maximum. Relative to **every** full-information maximizing pair $(P^H_{1f},P^H_{2f})$ of the high type, the equilibrium funding price is lower and its regular price is higher:
--   $$\dot P_1<P^H_{1f},\qquad \dot P_2>P^H_{2f}.$$
--   This characterizes the two-price signaling equilibrium and both price distortions.
--
--   **Formalization Note** The extra bound $T\le(3+\alpha)q_L/8$ corrects a false printed statement: without it, the low type can profitably mimic a dotted pair with $\dot P_2>q_L$. The optimum $\Pi^{L*}$ is a supremum of the model payoff over feasible prices, not a substituted closed form. Equilibrium means no profitable deviation under the paper's off-path low-quality beliefs. The comparison quantifies over full-information maximizers rather than defining them by the desired formula.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), pp. 26–27, Proposition 2; p. 41–43, Proof

import Mathlib
import Definitions.Def_CrowdSignal_TwoPrice_Setting

namespace CrowdSignal.TwoPrice

/-- Proposition 2, pp. 26–27, with the financing bound needed for its stated equilibrium. -/
theorem proposition_2 (P : Params) (hP : P.Standing)
    (hgap : P.qH ≤ (P.α ^ 2 + 6 * P.α + 25) * P.qL / 16)
    (hTL : P.T ≤ (3 + P.α) / 8 * P.qL)
    (Pd : ℝ × ℝ) (h2 : P.qH / 2 < Pd.2)
    (hline : 4 * Pd.1 + (1 - P.α) * Pd.2 = 2 * P.qH)
    (hW : W P P.qL P.qH Pd.1 Pd.2 = optPayoff P P.qL P.qL)
    (hT : P.T ≤ Pd.1) :
    IsSepEq2 P Pd ((3 + P.α) / 8 * P.qL, P.qL / 2) ∧
    SurvivesIC2 P Pd ((3 + P.α) / 8 * P.qL, P.qL / 2) ∧
    (∀ xH xL : ℝ × ℝ, IsSepEq2 P xH xL → SurvivesIC2 P xH xL →
      xH = Pd ∧
      IsGreatest (payoff P P.qL P.qL '' {x | Feas P x}) (payoff P P.qL P.qL xL) ∧
      xL = ((3 + P.α) / 8 * P.qL, P.qL / 2)) ∧
    (∀ xf : ℝ × ℝ, Feas P xf →
      IsGreatest (payoff P P.qH P.qH '' {x | Feas P x}) (payoff P P.qH P.qH xf) →
      Pd.1 < xf.1 ∧ xf.2 < Pd.2) := by sorry

end CrowdSignal.TwoPrice
