-- Prove2me | Theorems.Thm_BitDFT_GroupedUnaryAdvance_correct
-- name    : BitDFT.GroupedUnaryAdvance.correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T05:34:40.941707+00:00
-- url     : https://prove2.me/theorems/f0999aac-1e2c-4351-9f6b-a8d5ce60efee
-- title:
--   The grouped unary controller reaches the exact source offset
-- statement:
--   Let the counter tape contain exactly $3r+5$ consecutive one symbols from its current head, followed by a symbol other than one. The grouped controller skips the first five marks, then advances the source head once for every group of three marks, and finally advances once at the sentinel. It preserves tape contents and all unrelated heads, halts after exactly $3r+6$ transitions, and leaves the source head advanced by $r+1$ cells and the counter head advanced by $3r+5$ cells. This is the positioning adapter that converts the logarithmic scanner's unary output into the multiplier-product offset.
-- source:
--   Exact full-run proof for the published BitDFT_GroupedUnaryAdvance controller. The theorem is proved locally by a three-transition cycle, a five-step prefix, and induction on the number of groups; it supplies a coordinate-layout adapter for the rescaling construction.

import Definitions.Def_BitDFT_GroupedUnaryAdvance
import Mathlib.Tactic
open IntMul BitDFT.GroupedUnaryAdvance

theorem BitDFT.GroupedUnaryAdvance.correct (N : MultitapeTM) (source counter : Fin N.k)
    (hsc : source ≠ counter) (base : N.Cfg) (r sourceHead counterHead : ℕ)
    (hones : ∀ j, j < 3*r+5 → base.cells counter (counterHead+j) = N.one)
    (hstop : base.cells counter (counterHead+3*r+5) ≠ N.one) :
    (machine N source counter hsc).step^[3*r+6]
      (frame N source counter hsc base (.skip 0) sourceHead counterHead) =
      frame N source counter hsc base .halt (sourceHead+r+1) (counterHead+3*r+5) := by sorry
