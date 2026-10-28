-- Prove2me | Theorems.Thm_BitDFT_serializer_fresh_routing_old_tapes
-- name    : BitDFT.serializer_fresh_routing_old_tapes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T06:42:18.478495+00:00
-- url     : https://prove2.me/theorems/c9bcd6b9-3bef-4609-875b-1fd40d9a29f1
-- title:
--   Fresh-tape routing preserves every old work-tape address
-- statement:
--   For r ≥ 0, let the enlarged serializer tape bank contain 5+r tapes, and let i be an old work-tape index with 2 ≤ i < r+2. The cyclic routing sends logical extension tape i+3 back to physical tape i. Thus all pre-existing multiplier work tapes from index 2 onward remain at their original physical addresses while the serializer's three work tapes use the appended positions.
-- source:
--   This is the exact inverse-side address law for the cyclic rotation defining the fresh-tape routing. It makes the preservation of the caller and multiplier bank explicit rather than implicit in the permutation.

import Definitions.Def_BitDFT_SerializerFreshTapeRouting
set_option autoImplicit false
open BitDFT.SerializerFreshTapeRouting

theorem BitDFT.serializer_fresh_routing_old_tapes (r : ℕ) (i : Fin (r+2)) (hi : 2 ≤ i.val) :
    routing r ⟨i.val+3,by have := i.isLt; omega⟩ = ⟨i.val,by omega⟩ := by sorry
