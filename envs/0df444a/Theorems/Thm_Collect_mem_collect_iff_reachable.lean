-- Prove2me | Theorems.Thm_Collect_mem_collect_iff_reachable
-- name    : Collect.mem_collect_iff_reachable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T07:06:03.364599+00:00
-- url     : https://prove2.me/theorems/870de666-1589-4f26-9e0c-6c208b9486d6
-- title:
--   Collect: mem collect iff reachable
-- statement:
--   The Collect construction uses the mem collect iff reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L470-L471
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L470-L471

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Collect
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect

theorem Collect.mem_collect_iff_reachable {O : OBdd n m} {j : Fin m} :
    j ∈ collect O ↔ Pointer.Reachable O.1.heap O.1.root (.node j) := by sorry
