-- Prove2me | Theorems.Thm_BDD_relabel_dependsOn
-- name    : BDD.relabel_dependsOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:22:06.505784+00:00
-- url     : https://prove2.me/theorems/bdadb25a-790b-4315-8487-f904e39f0979
-- title:
--   BDD: relabel depends On
-- statement:
--   The BDD construction uses the relabel depends On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L505-L596
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L505-L596

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

theorem BDD.relabel_dependsOn {n} {B : BDD} {f : Fin B.nvars → Fin n} {hf h i} :
  Nary.DependsOn ((B.relabel f hf).denotation h) i ↔
  ∃ j, i = f j ∧ Nary.DependsOn B.denotation' j := by sorry
