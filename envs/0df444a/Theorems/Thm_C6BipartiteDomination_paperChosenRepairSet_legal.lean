-- Prove2me | Theorems.Thm_C6BipartiteDomination_paperChosenRepairSet_legal
-- name    : C6BipartiteDomination.paperChosenRepairSet_legal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:11.31919+00:00
-- url     : https://prove2.me/theorems/4c3468af-76bd-414e-a878-c4e79847836f
-- title:
--   C6 Bipartite Domination: paper Chosen Repair Set legal
-- statement:
--   The C6 Bipartite Domination construction uses the paper Chosen Repair Set legal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L61-L72
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L61-L72

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paperChosenRepairSet_legal
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    ∀ u ∈ paperChosenRepairSet G D hCan hmax w,
      IsRepairVertex G D w u := by sorry
