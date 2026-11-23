-- Prove2me | Theorems.Thm_BDD_denotation_congr
-- name    : BDD.denotation_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:22:38.0108+00:00
-- url     : https://prove2.me/theorems/2e4a76b4-3fbd-41a6-90a7-5bf56258047d
-- title:
--   BDD: denotation congr
-- statement:
--   The BDD construction uses the denotation congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L141-L144
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L141-L144

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

theorem BDD.denotation_congr {B : BDD}
    {I : Vector Bool n} {J : Vector Bool m} {hn : B.nvars ≤ n} {hm : B.nvars ≤ m} :
    (∀ i : Fin B.nvars, I[i] = J[i]) → B.denotation hn I = B.denotation hm J := by sorry
