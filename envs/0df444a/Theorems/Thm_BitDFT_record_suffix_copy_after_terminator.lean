-- Prove2me | Theorems.Thm_BitDFT_record_suffix_copy_after_terminator
-- name    : BitDFT.record_suffix_copy_after_terminator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:21:22.397374+00:00
-- url     : https://prove2.me/theorems/9402378b-7723-471f-be24-d54b4339fe3a
-- title:
--   Compose separator insertion with workspace suffix copying
-- statement:
--   Suppose a halted native extraction configuration has a blank scratch cell under its head, and inserting a separator makes its complete workspace exactly the routed suffix-copier frame. Then two transitions perform the extractor-to-terminator handoff and separator insertion, followed by one copier handoff, one transition per suffix bit, and a final separator check. The complete run takes |r|+4 transitions and ends in the exact embedded halted copier configuration.
-- source:
--   Composition of the accepted separator insertion theorem with the exact finite-time suffix-copy adapter.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.record_suffix_copy_after_terminator (M : MultitapeTM)
    (b : (host M).Cfg)
    (hstate : b.state = (host M).qHalt)
    (hblank : b.cells (sourceTape M) (b.head (sourceTape M)) = (host M).blank)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool)
    (hworkspace : Function.update b.cells (sourceTape M)
      (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep) =
        (embed M cells heads rootCells rootHead
          (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).cells)
    (hheads : b.head = (embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))).head) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+4]
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) =
      BitDFT.MachineSequence.rightCfg P Q
        ⟨(embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).state,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).cells,
          (embed M cells heads rootCells rootHead
            (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
              (pre.length+rest.length+1))).head⟩ := by sorry
