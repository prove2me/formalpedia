-- Prove2me | Theorems.Thm_Collect_collect_spec
-- name    : Collect.collect_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:58:09.633789+00:00
-- url     : https://prove2.me/theorems/2aafb3f6-8a2c-4ff7-b63b-df16a5e5b7eb
-- title:
--   Collect: collect spec
-- statement:
--   `collect` is correct.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L360-L371
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L360-L371

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Collect
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect

theorem Collect.collect_spec {O : OBdd n m} {j : Fin m} : Pointer.Reachable O.1.heap O.1.root (.node j) → j ∈ collect O := by sorry
