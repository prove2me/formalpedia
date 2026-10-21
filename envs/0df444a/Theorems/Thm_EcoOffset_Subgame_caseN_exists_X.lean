-- Prove2me | Theorems.Thm_EcoOffset_Subgame_caseN_exists_X
-- name    : EcoOffset.Subgame.caseN_exists_X
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:08.847637+00:00
-- url     : https://prove2.me/theorems/43edebd1-04f5-4be8-bee8-6c87b1b7bbd3
-- title:
--   Proof of Proposition 1, Online Supplement p. 24 (PDF 57) — Case N: if βc < B2 then X = min{g | h(g) = 0} exists and X > 0
-- statement:
--   Assume the standing assumptions of the model, Case N ($\beta_u=1$), $\alpha>0$ and $e_o>0$, and let $h$ be as in the previous statement. If $\beta_c<B_2$, then there is $X>0$ with
--   $$h(X)=0\qquad\text{and}\qquad h(g)>0\ \text{ for all } g\in[0,X),$$
--   that is, $X=\min\{g\ge0: h(g)=0\}$ exists and is positive.
--
--   $X$ is the offset price at which the firm becomes indifferent between covering the whole market and serving only the high-value consumers; Proposition 1(i) compares best responses on either side of it.
--
--   **Formalization Note** The page derives existence from $\lim_{g\to\infty}h'(g)=-e_o\alpha(1-\beta_c)m<0$, which requires $e_o>0$; that hypothesis is added. The least zero is encoded by the two displayed properties.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 24 (PDF 57), proof of Proposition 1 ('Note that lim h′(g) = −eoα(1−βc)m < 0 … then there exists X = min{g|h(g) = 0} and X > 0')

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 24: in Case N, if `βc < B2` (and `eo > 0`),
then `X = min {g | h(g) = 0}` exists and `X > 0`: there is `X > 0` with `h(X) = 0` and `h > 0`
on `[0, X)`. -/
theorem caseN_exists_X (P : Params) (hS : P.Standing) (hβu : P.βu = 1) (hα : 0 < P.α)
    (heo : 0 < P.eo) (hB2 : P.βc < B2 P) :
    ∃ X : ℝ, 0 < X ∧ hN P X = 0 ∧ ∀ g ∈ Set.Ico 0 X, 0 < hN P g := by sorry

end EcoOffset.Subgame
