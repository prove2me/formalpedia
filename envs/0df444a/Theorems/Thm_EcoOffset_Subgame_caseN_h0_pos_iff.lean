-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseN_h0_pos_iff
-- name    : EcoOffset.Subgame.caseN_h0_pos_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:02.231299+00:00
-- url     : https://prove2.me/theorems/df2ced13-1762-4ccb-a147-0b6211a46f31
-- title:
--   Proof of Proposition 1, Online Supplement p. 24 (PDF 57) — Case N: h(0) > 0 if and only if βc < B2
-- statement:
--   Assume the standing assumptions of the model, Case N ($\beta_u=1$) and $\alpha>0$. Let
--   $$h(g)=\pi(v_l,e_{g,1},e_{g,1}+e_o\mid g)-\pi(v_h,e_{g,1-\alpha+\alpha\beta_c},e_{g,1-\alpha+\alpha\beta_c}+e_o\mid g).$$
--   Then
--   $$h(0)>0\iff \beta_c<B_2=\frac{\frac{v_l-c(\bar e)}{v_h-c(\bar e)}-1+\alpha}{\alpha}.$$
--
--   At a zero offset price, selling to everyone beats selling only to high-value consumers exactly when the share of high-value eco-conscious consumers is below $B_2$. This is the upper threshold of the interval $(B_1,B_2)$ in Proposition 1(i).
--
--   **Formalization Note** $\alpha>0$ is added because $B_2$ divides by $\alpha$.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 24 (PDF 57), proof of Proposition 1 ('if h(0) > 0 (i.e., βc < B2 ≜ …)')

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 24: in Case N, `h(0) > 0` if and only if
`βc < B2 = ((vl − c(¯e))/(vh − c(¯e)) − 1 + α)/α`. -/
theorem caseN_h0_pos_iff (P : Params) (hS : P.Standing) (hβu : P.βu = 1) (hα : 0 < P.α) :
    0 < hN P 0 ↔ P.βc < B2 P := by sorry

end EcoOffset.Subgame
