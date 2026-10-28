-- Prove2me | Theorems.Thm_BitDFT_record_suffix_copy_handoff
-- name    : BitDFT.record_suffix_copy_handoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:21:30.991371+00:00
-- url     : https://prove2.me/theorems/e4607aff-6342-4b3d-aef4-cad97425611c
-- title:
--   Run the routed suffix copier after controller handoff
-- statement:
--   Once the record-terminator controller has finished and the caller workspace matches the embedded two-tape copier frame, one stationary controller handoff followed by the copier's exact run produces the embedded final configuration. For a suffix of length |r|, the complete composed machine takes |r|+2 steps: one handoff, |r| copied bits, and one separator check.
-- source:
--   Composition of controller sequencing with the exact-runtime caller-workspace suffix-copy adapter.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.record_suffix_copy_handoff (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    let initial := embed M cells heads rootCells rootHead
      (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+2]
      (BitDFT.MachineSequence.leftCfg P Q ⟨P.exit,initial.cells,initial.head⟩) =
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
