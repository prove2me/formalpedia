-- Prove2me | Theorems.Thm_BIInsurance_Screening_proposition_4
-- name    : BIInsurance.Screening.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:05.722913+00:00
-- url     : https://prove2.me/theorems/961a75ce-f9f9-4061-9ecd-13116d54cef5
-- title:
--   Proposition 4, p. 20 — the insurer's optimal menu gives the low-demand firm weakly higher coverage and premium: s∗_L ≥ s∗_H, y∗_L ≥ y∗_H
-- statement:
--   Assume the standing assumptions of the model (with one waiting period $w=w_H=w_L$), the condition $K>\mu_H+\delta_H+\gamma\ln\frac{(T-\tau)p-c}{c}$, and condition (5.5) — the hypotheses the paper adopts "throughout the sequel" (p. 19). Consider the insurer's screening problem (5.1): choose a menu $(y_H,s_H)$, $(y_L,s_L)$ with $s_H,s_L\in[0,\bar s]$ maximizing the expected premium income net of expected claims,
--
--   $$
--   \alpha\{y_H-\text{claims}_H(s_H)\}+(1-\alpha)\{y_L-\text{claims}_L(s_L)\},
--   $$
--
--   subject to the incentive-compatibility constraints (IC-HL), (IC-LH) and the participation constraints (IR-H), (IR-L), where the firm's profits are evaluated with its optimal recovery effort $e^*$. Then:
--   1. the problem has an optimal menu;
--   2. every optimal menu $(y^*_H,s^*_H,y^*_L,s^*_L)$ satisfies
--
--   $$
--   s^*_L\ge s^*_H\qquad\text{and}\qquad y^*_L\ge y^*_H .
--   $$
--
--   The low-demand firm is sold the richer and more expensive contract, the reverse of the order in standard screening models, because the low-demand firm values coverage more (Proposition 2).
--
--   **Formalization Note** The page's "the optimal contracts" presupposes that (5.1) has an optimum; existence is stated as the first conjunct so that the second is not vacuous. The added standing hypotheses $\rho>0$ and $w<T-\tau$ are necessary: at $\rho=0$ or $w=T-\tau$ insurance pays nothing and every menu with zero premiums is optimal, so the ordering fails.
-- source:
--   Kao, Keskin & Shang, Impact of information asymmetry and limited production capacity on business interruption insurance, SSRN 3184530 (version of May 13, 2020), p. 20, Proposition 4; standing conditions p. 19; proof p. 36

import Mathlib
import Definitions.Def_BIInsurance_Screening_Model

namespace BIInsurance.Screening

theorem proposition_4 (P : Params) (hS : P.Standing) (hK : KCond P) (h55 : Cond55 P) :
    (∃ M : Menu, IsOptimalMenu P M) ∧
      ∀ M : Menu, IsOptimalMenu P M → M.sH ≤ M.sL ∧ M.yH ≤ M.yL := by sorry

end BIInsurance.Screening
