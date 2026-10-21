-- Prove2me | Theorems.Thm_EcoOffset_Subgame_lemma_VI1
-- name    : EcoOffset.Subgame.lemma_VI1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:08.07198+00:00
-- url     : https://prove2.me/theorems/136a871b-eb51-43f9-8011-4ab0e7b6edc2
-- title:
--   Lemma VI1, Online Supplement p. 24 (PDF 57) — e_{x,a} is weakly decreasing in both x and a
-- statement:
--   Assume the standing assumptions of the model, and let $e_{x,a}$ be the segment-optimal emission. If $0\le x\le x'$, $0\le a\le a'\le 1$, then
--   $$e_{x',a}\le e_{x,a}\qquad\text{and}\qquad e_{x,a'}\le e_{x,a}.$$
--
--   A higher marginal offset cost $x$ or a larger served segment $a$ makes the firm abate more (choose lower controllable emissions). This is the comparison the proof of Proposition 1 uses to compare emissions before and after the market expands.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), Online Supplement p. 24 (PDF 57), Lemma VI1

import Mathlib
import Definitions.Def_EcoOffset_Subgame_Model

namespace EcoOffset.Subgame

/-- Lemma VI1: `e_{x,a}` is weakly decreasing in both `x` and `a` (for `a ∈ [0, 1]`). -/
theorem lemma_VI1 (P : Params) (hS : P.Standing) {x x' a a' : ℝ}
    (hx0 : 0 ≤ x) (ha : 0 ≤ a) (haa : a ≤ a') (ha' : a' ≤ 1) (hx : x ≤ x') :
    segOpt P x' a ≤ segOpt P x a ∧ segOpt P x a' ≤ segOpt P x a := by sorry

end EcoOffset.Subgame
