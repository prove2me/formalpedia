-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_paper10SpecialQSet
-- name    : C6BipartiteDomination.mem_paper10SpecialQSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:39.731483+00:00
-- url     : https://prove2.me/theorems/f0beebd8-e7c9-4af2-9fa8-df4ac05fd586
-- title:
--   C6 Bipartite Domination: mem paper10 Special QSet
-- statement:
--   The C6 Bipartite Domination construction uses the mem paper10 Special QSet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L56-L61
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L56-L61

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_paper10SpecialQSet
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) (q : V) :
    q ∈ paper10SpecialQSet G hCan hmax ↔ IsPaper10SpecialQ G hCan hmax q := by sorry
