-- Prove2me | Theorems.Thm_Collect_collect_terminal
-- name    : Collect.collect_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:00:56.723946+00:00
-- url     : https://prove2.me/theorems/81c84329-3813-4b85-a510-c9cacf4e77cd
-- title:
--   Collect: collect terminal
-- statement:
--   The Collect construction uses the collect terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L34-L36
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Collect.lean#L34-L36

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Collect
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect

theorem Collect.collect_terminal {O : OBdd n m} (h : O.1.root = .terminal b) :
    collect O = [] := by sorry
