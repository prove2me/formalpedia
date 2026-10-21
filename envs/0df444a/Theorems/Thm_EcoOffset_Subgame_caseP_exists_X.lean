-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseP_exists_X
-- name    : EcoOffset.Subgame.caseP_exists_X
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:04.344983+00:00
-- url     : https://prove2.me/theorems/2d170056-cb5a-4a13-83d3-9744c118919e
-- title:
--   Proof of Proposition 1, Online Supplement p. 25 (PDF 58) — Case P: if βu < ˜B2 then h(0) > 0 and X = min{g | h(g) = 0} > 0 exists
-- statement:
--   Assume the standing assumptions of the model, Case P ($\beta_c=1$), $\alpha<1$ and $v_h-v_l<\xi e_o$. Let
--   $$h(g)=\pi\big(v_l,e_{g,1},e_{g,1}+e_o-\tfrac{v_h-v_l}{\xi}\;\big|\;g\big)-\pi(v_h,e_{g,\alpha+(1-\alpha)\beta_u},e_{g,\alpha+(1-\alpha)\beta_u}+e_o\mid g).$$
--   If
--   $$\beta_u<\tilde B_2=\min\Big(\frac{(v_l-c(\bar e))-(v_h-c(\bar e))\alpha}{(v_h-c(\bar e))(1-\alpha)},\ \frac{\xi e_o(1-\alpha)-(v_h-v_l)}{\xi e_o(1-\alpha)}\Big),$$
--   then $h(0)>0$, and there is $X>0$ with $h(X)=0$ and $h(g)>0$ for all $g\in[0,X)$.
--
--   The first term of the minimum is the condition $h(0)>0$, the second the condition $\lim_{g\to\infty}h'(g)<0$; together they give the switching price $X$ of Proposition 1(ii).
--
--   **Formalization Note** $\alpha<1$ is added because $\tilde B_2$ divides by $1-\alpha$. The least zero is encoded by $h(X)=0$ and $h>0$ on $[0,X)$.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 25 (PDF 58), proof of Proposition 1, Case P ('If h(0) > 0 and lim h′(g) < 0 (i.e., βu < ˜B2 ≜ …), then there exists X …')

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 25: in Case P with `vh − vl < ξ eo`, if
`βu < ˜B2` then `h(0) > 0` and `X = min {g | h(g) = 0}` exists with `X > 0`. -/
theorem caseP_exists_X (P : Params) (hS : P.Standing) (hβc : P.βc = 1) (hα : P.α < 1)
    (hv : P.vh - P.vl < P.ξ * P.eo) (hB2 : P.βu < B2P P) :
    0 < hP P 0 ∧ ∃ X : ℝ, 0 < X ∧ hP P X = 0 ∧ ∀ g ∈ Set.Ico 0 X, 0 < hP P g := by sorry

end EcoOffset.Subgame
