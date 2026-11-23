-- Prove2me | Theorems.Thm_Collect_collect_nodup
-- name    : Collect.collect_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:59.4258+00:00
-- url     : https://prove2.me/theorems/c9b123de-b4d2-4e7f-8f12-3fea0cf4205a
-- title:
--   Collect: collect nodup
-- statement:
--   The Collect construction uses the collect nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L473-L475
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L473-L475

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Collect
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect

theorem Collect.collect_nodup {O : OBdd n m} : (collect O).Nodup := by sorry
