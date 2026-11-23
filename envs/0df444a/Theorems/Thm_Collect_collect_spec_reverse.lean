-- Prove2me | Theorems.Thm_Collect_collect_spec_reverse
-- name    : Collect.collect_spec_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:53.247736+00:00
-- url     : https://prove2.me/theorems/f2ef4e9b-f283-4f39-aeec-ef2d7eaca4ff
-- title:
--   Collect: collect spec reverse
-- statement:
--   The Collect construction uses the collect spec reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L431-L437
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L431-L437

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Collect
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect

theorem Collect.collect_spec_reverse {O : OBdd n m} {j : Fin m} :
    j ∈ collect O → Pointer.Reachable O.1.heap O.1.root (.node j) := by sorry
