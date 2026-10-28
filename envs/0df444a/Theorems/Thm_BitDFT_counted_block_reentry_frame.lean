-- Prove2me | Theorems.Thm_BitDFT_counted_block_reentry_frame
-- name    : BitDFT.counted_block_reentry_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T01:02:14.676275+00:00
-- url     : https://prove2.me/theorems/5d95f0b6-7a11-4572-a063-ca8195f52301
-- title:
--   A copied block leaves the exact re-entry frame for the next block
-- statement:
--   Suppose a counted copier consumes the next $m=\operatorname{val}(y)+1$ bits from a remaining input word $x$, appending them to output prefix $o$. When its counter and saved-template tapes have reset, entering the same copier again gives exactly the frame with updated prefixes $p\Vert\operatorname{take}(m,x)$ and $o\Vert\operatorname{take}(m,x)$ and remaining suffix $\operatorname{drop}(m,x)$. The source and output heads are already at the next block boundaries. This is the exact machine-state invariant needed to iterate the counted block copier over a vector.
-- source:
--   Concrete tape-frame recurrence for repeatedly invoking the accepted counted-block machine as a vector scanner.

import Definitions.Def_BitDFT_CountedBlock
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
set_option autoImplicit false
open IntMul

theorem BitDFT.counted_block_reentry_frame (pre out x y : List Bool)
    (hx : IntMul.val y + 1 ≤ x.length) :
    let m := IntMul.val y + 1
    (⟨.emit,
      (BitDFT.CountedBlock.frame pre out x y y.reverse m .halt).cells,
      (BitDFT.CountedBlock.frame pre out x y y.reverse m .halt).head⟩ :
        IntMul.CountedStream.machine.Cfg) =
      BitDFT.CountedBlock.frame (pre ++ x.take m) (out ++ x.take m)
        (x.drop m) y y.reverse 0 .emit := by sorry
