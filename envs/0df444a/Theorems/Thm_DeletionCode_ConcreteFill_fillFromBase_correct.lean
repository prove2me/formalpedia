-- Prove2me | Theorems.Thm_DeletionCode_ConcreteFill_fillFromBase_correct
-- name    : DeletionCode.ConcreteFill.fillFromBase_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:09:33.559249+00:00
-- url     : https://prove2.me/theorems/00f4e01c-1d00-4e6d-97db-b344dbc78ef0
-- title:
--   Concrete Fill: fill From Base correct
-- statement:
--   A valid base occurrence is filled exactly, using only its stored seed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean#L38-L56
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean#L38-L56

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
import Definitions.Def_DeletionCode_ConcreteFill
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteFill
open Windows PartialWords

theorem DeletionCode.ConcreteFill.fillFromBase_correct (x p : Letters) (n k L : ℕ)
    (s : Memory) (m start r : ℕ) (seed : Bits k)
    (hx : KUnique x n k) (hs : Sound s p m)
    (hbound : start + L ≤ m) (hr : r + k ≤ L)
    (hread : readBits s (start + r) k = some seed)
    (hocc : ∃ a, a + L ≤ n ∧ Agree x a p start L) :
    ∃ t, fillFromBase x n k L s m start r = some t ∧
      Recovered s t p m start L := by sorry
