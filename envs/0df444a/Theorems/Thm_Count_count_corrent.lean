-- Prove2me | Theorems.Thm_Count_count_corrent
-- name    : Count.count_corrent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:31.095818+00:00
-- url     : https://prove2.me/theorems/2e3bdbc6-7029-47d9-997f-02faa068f8ec
-- title:
--   Count: count corrent
-- statement:
--   The Count construction uses the count corrent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Count.lean#L319-L322
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Count.lean#L319-L322

import Definitions.Def_Bdd_Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Std.Data.HashMap.Lemmas
import Definitions.Def_Bdd_Count
set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
open Count

theorem Count.count_corrent {O : OBdd n m} : count O = numSolutions O := by sorry
