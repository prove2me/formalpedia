-- Prove2me | Theorems.Thm_BDD_denotation_eq_of_denotation_eq
-- name    : BDD.denotation_eq_of_denotation_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:22:01.864961+00:00
-- url     : https://prove2.me/theorems/59d1efd7-ffdd-41e9-a01e-10f6cd570170
-- title:
--   BDD: denotation eq of denotation eq
-- statement:
--   If two `BDD` have the same `denotation` with respect to some input size `n`, then they have the same `denotation` with respect to any other input size `m` as well.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L147-L152
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/BDD.lean#L147-L152

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

theorem BDD.denotation_eq_of_denotation_eq {B C : BDD} (hn : B.nvars ⊔ C.nvars ≤ n) (hm : B.nvars ⊔ C.nvars ≤ m) :
    B.denotation (n := n) (by omega) = C.denotation (n := n) (by omega) →
    B.denotation (n := m) (by omega) = C.denotation (n := m) (by omega) := by sorry
