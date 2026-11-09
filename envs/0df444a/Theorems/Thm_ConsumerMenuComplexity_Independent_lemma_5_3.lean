-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_lemma_5_3
-- name    : ConsumerMenuComplexity.Independent.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:07:28.69241+00:00
-- url     : https://prove2.me/theorems/50010eb3-1c27-4297-a33f-8530bb861e18
-- title:
--   Lemma 5.3 — both projection identities
-- statement:
--   Let $S$ be any valid menu with the null option, feasible allocation-price triples, and an actual maximizing selection $M$ at every nonnegative type. Let $M^{\rm proj}$ be the actual same-price projection defined from those axis choices. Then it selects a maximizer from the projected menu and
--   $$u^{M^{\rm proj}}(v_1,v_2)=\max\{u^M(v_1,0),u^M(0,v_2)\}.$$
--   Both axis identities hold for every nonnegative coordinate:
--   $$u^M(a,0)=u^{M^{\rm proj}}(a,0),\qquad u^M(0,b)=u^{M^{\rm proj}}(0,b).$$
--   This describes the utilities retained by projection, including boundary reports and all maximizing ties. No prior or utility differentiability hypothesis is needed.
--
--   Differences from the source:
--   - encoding: any menu and its projected menu → valid option sets with actual selections, and the defined axis-choice projection; reason: the same-price splitting in the source proof supplies the maximizing choices, with item 1 preferred in an axis-utility tie
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Lemma 5.3, PDF p.17 (printed p.16)

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Transforms
open scoped NNReal

namespace ConsumerMenuComplexity.Independent

/-- Lemma 5.3, PDF p.17 (printed p.16). Actual projection at the same prices. -/
theorem lemma_5_3 (S : Set Option) (M : Mechanism)
    (hS : ValidMenu S) (hchoice : Selects S M) :
    Selects (projectMenu S) (projected M) ∧
    (∀ v : TypeSpace, utility (projected M) v =
      max (utility M (typeAt (v 0) 0)) (utility M (typeAt 0 (v 1)))) ∧
    (∀ a : ℝ≥0, utility M (typeAt a 0) = utility (projected M) (typeAt a 0)) ∧
    (∀ b : ℝ≥0, utility M (typeAt 0 b) = utility (projected M) (typeAt 0 b)) := by sorry

end ConsumerMenuComplexity.Independent
