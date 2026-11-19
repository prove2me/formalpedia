-- Prove2me | Theorems.Thm_DeletionCode_ConcreteFill_loadRoot_correct
-- name    : DeletionCode.ConcreteFill.loadRoot_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:12.736802+00:00
-- url     : https://prove2.me/theorems/8c862355-cd51-436d-bd01-80f7528bd0af
-- title:
--   Concrete Fill: load Root correct
-- statement:
--   The Concrete Fill construction uses the load Root correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean#L81-L94
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean#L81-L94

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
import Definitions.Def_DeletionCode_ConcreteFill
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteFill
open Windows PartialWords

theorem DeletionCode.ConcreteFill.loadRoot_correct (x p : Letters) (n a len : ℕ) (s : Memory) (m : ℕ)
    (hs : Sound s p m) (ha : a + len ≤ n) (hbound : len ≤ m)
    (hocc : Agree x a p 0 len) :
    ∃ t, loadRoot x n a len s m = some t ∧ Recovered s t p m 0 len := by sorry
