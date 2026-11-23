-- Prove2me | Theorems.Thm_BDD_count_eq_card
-- name    : BDD.count_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:22:08.287962+00:00
-- url     : https://prove2.me/theorems/1e9b6751-cbca-4170-a105-a00ee27f0958
-- title:
--   BDD: count eq card
-- statement:
--   The BDD construction uses the count eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L810-L811
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L810-L811

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
attribute [local implicit_reducible] restrict restrict'

theorem BDD.count_eq_card {B : BDD} : B.count = Fintype.card { I // B.denotation' I = true } := by sorry
