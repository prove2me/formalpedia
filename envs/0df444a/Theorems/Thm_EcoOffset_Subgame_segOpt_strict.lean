-- Prove2me | Theorems.Thm_EcoOffset_Subgame_segOpt_strict
-- name    : EcoOffset.Subgame.segOpt_strict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:59.531423+00:00
-- url     : https://prove2.me/theorems/c775c2b4-0d24-4466-95a1-635646b17850
-- title:
--   Proof of Proposition 1, Online Supplement p. 24 (PDF 57) — e_{x,1} < e_{x,a} for a < 1 when e_{x,1} < ē and e_{x,a} > 0
-- statement:
--   Assume the standing assumptions of the model. Let $x\ge0$ and $0\le a<1$. If $e_{x,1}<\bar e$ and $e_{x,a}>0$, then
--   $$e_{x,1}<e_{x,a}.$$
--
--   Lemma VI1 gives $e_{x,1}\le e_{x,a}$; this is the strict version the proof of Proposition 1 invokes when it says the emissions inequality "is strict if $\bar e$ is large enough". The two conditions make precise what "large enough" is needed for: neither optimum sits at the end of the interval where the comparison could tie.
--
--   **Formalization Note** The paper's "if $\bar e$ is large enough" is replaced by the explicit interiority conditions $e_{x,1}<\bar e$ and $0<e_{x,a}$.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 24 (PDF 57), proof of Proposition 1 ('the inequality is due to Lemma VI1 and is strict if ē is large enough')

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Proof of Proposition 1, Online Supplement p. 24: the comparison of Lemma VI1 between the
segment sizes `a < 1` and `1` is strict when `e_{x,1} < ¯e` and `0 < e_{x,a}`. -/
theorem segOpt_strict (P : Params) (hS : P.Standing) (x a : ℝ) (hx : 0 ≤ x)
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (h1 : segOpt P x 1 < P.ebar) (h2 : 0 < segOpt P x a) :
    segOpt P x 1 < segOpt P x a := by sorry

end EcoOffset.Subgame
