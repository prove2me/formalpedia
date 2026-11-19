-- Prove2me | Theorems.Thm_DeletionCode_ConcreteFill_copyFromMemory_correct
-- name    : DeletionCode.ConcreteFill.copyFromMemory_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:13:09.118137+00:00
-- url     : https://prove2.me/theorems/683d8a95-8bd9-4b96-9fc9-7629db435359
-- title:
--   Concrete Fill: copy From Memory correct
-- statement:
--   Supplier copying preserves truth when the recorded blocks really agree.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean#L59-L79
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean#L59-L79

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
import Definitions.Def_DeletionCode_ConcreteFill
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteFill
open Windows PartialWords

theorem DeletionCode.ConcreteFill.copyFromMemory_correct (source s : Memory) (q p : Letters)
    (sourceLength sourceStart len m start : ℕ) (bits : Bits len)
    (hsource : Sound source q sourceLength) (hs : Sound s p m)
    (hsourceBound : sourceStart + len ≤ sourceLength) (hbound : start + len ≤ m)
    (hread : readBits source sourceStart len = some bits)
    (hagree : Agree q sourceStart p start len) :
    ∃ t, copyFromMemory source sourceLength sourceStart len s m start = some t ∧
      Recovered s t p m start len := by sorry
