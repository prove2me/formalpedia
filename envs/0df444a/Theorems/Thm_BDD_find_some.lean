-- Prove2me | Theorems.Thm_BDD_find_some
-- name    : BDD.find_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:20:44.441844+00:00
-- url     : https://prove2.me/theorems/3f5f02df-103f-46da-99c6-df968580d4aa
-- title:
--   BDD: find some
-- statement:
--   The BDD construction uses the find some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L646-L651
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L646-L651

import Definitions.Def_Bdd_Reduce
import Definitions.Def_Bdd_Apply
import Definitions.Def_Bdd_Relabel
import Definitions.Def_Bdd_Choice
import Definitions.Def_Bdd_Restrict
import Definitions.Def_Bdd_Evaluate
import Definitions.Def_Bdd_Sim
import Definitions.Def_Bdd_Size
import Definitions.Def_Bdd_Count
import Definitions.Def_Bdd_BDD
set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered Lift.olift Relabel.orelabel Reduce.oreduce
open BDD
attribute [local implicit_reducible] lift
attribute [local implicit_reducible] denotation
attribute [local implicit_reducible] const var apply
attribute [local implicit_reducible] relabel'' relabel'

theorem BDD.find_some {B : BDD} {I} : B.find = some I → B.denotation' I = true := by sorry
