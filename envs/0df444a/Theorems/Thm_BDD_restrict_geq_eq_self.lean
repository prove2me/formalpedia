-- Prove2me | Theorems.Thm_BDD_restrict_geq_eq_self
-- name    : BDD.restrict_geq_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:22:12.904321+00:00
-- url     : https://prove2.me/theorems/6f134861-ef28-4842-880a-03c954bc122e
-- title:
--   BDD: restrict geq eq self
-- statement:
--   The BDD construction uses the restrict geq eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L667-L672
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L667-L672

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

theorem BDD.restrict_geq_eq_self {B : BDD} : i ≥ B.nvars → B.restrict b i = B := by sorry
