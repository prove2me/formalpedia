-- Prove2me | Theorems.Thm_BDD_SemanticEquiv_equivalence
-- name    : BDD.SemanticEquiv.equivalence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:22:12.080057+00:00
-- url     : https://prove2.me/theorems/4879bd6a-c034-4b9e-a85f-ef0b5b737054
-- title:
--   Semantic Equiv: equivalence
-- statement:
--   `SemanticEquiv` is an equivalence relation on `BDD`.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L155-L166
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L155-L166

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

theorem BDD.SemanticEquiv.equivalence : Equivalence SemanticEquiv := by sorry
