-- Prove2me | Theorems.Thm_BitDFT_first_coordinate_postprocess_composed_run_v2
-- name    : BitDFT.first_coordinate_postprocess_composed_run_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T21:47:29.253047+00:00
-- url     : https://prove2.me/theorems/b8277e32-d0cd-4c0f-8926-6d164a4d33ae
-- title:
--   Charge coordinate extraction and record postprocessing in one run
-- statement:
--   Suppose a vector preparation machine halts with a valid input vector, precision descriptors, and work tapes. The signed first-coordinate extractor runs, then the separator, rewind, and copy controllers run as a single continuation. The composed machine reaches exactly the continuation’s output configuration; its total clock includes the extraction time, one sequence handoff, and the full postprocessing bound.
-- source:
--   The accepted first-coordinate execution theorem, the accepted coordinate-to-copy theorem, and the generic finite-controller sequence bound.

import Definitions.Def_BitDFT_BeginAtStateV2
import Definitions.Def_BitDFT_FirstCoordinate
import Definitions.Def_BitDFT_RecordSuffixCopy
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_signed_block_final_slots
import Theorems.Thm_BitDFT_machine_sequence_bound
import Theorems.Thm_BitDFT_extraction_ready
import Theorems.Thm_BitDFT_signed_block_initial_match
import Theorems.Thm_BitDFT_signed_block_placement_correct
open BitDFT.RecordSuffixCopy BitDFT.SuffixCopyTwoTape IntMul

theorem BitDFT.first_coordinate_postprocess_composed_run_v2 (M : MultitapeTM)
    (c : (BitDFT.VectorReady.machine M).Cfg)
    (input extra : List Bool) (T : ℕ)
    (hrun : (BitDFT.VectorReady.machine M).step^[T]
      ((BitDFT.VectorReady.machine M).initCfg input extra) = c)
    (hhalt : c.state = (BitDFT.VectorReady.machine M).qHalt)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (sign : Bool) (x y : List Bool)
    (hroot : c.cells ⟨0,by change 0 < 4+(M.k+3); omega⟩ =
      fun p => PreprocessorAlphabet.encode (BitDFT.VectorReady.machine M) (rootCells p))
    (hrootHead : c.head ⟨0,by change 0 < 4+(M.k+3); omega⟩ = rootHead)
    (hv : c.cells ⟨1,by change 1 < 4+(M.k+3); omega⟩ =
      (BitDFT.VectorReady.machine M).tapeOf ((sign::x).map (BitDFT.VectorReady.machine M).bitSym))
    (hvHead : c.head ⟨1,by change 1 < 4+(M.k+3); omega⟩ = 1)
    (hc : c.cells (BitDFT.DescriptorPlacement.counterTape M.k) =
      (BitDFT.VectorReady.machine M).tapeOf
        ((BitDFT.VectorReady.machine M).sep :: (y.map (BitDFT.VectorReady.machine M).bitSym ++
          [(BitDFT.VectorReady.machine M).sep])))
    (hcHead : c.head (BitDFT.DescriptorPlacement.counterTape M.k) = y.length+1)
    (ht : c.cells (BitDFT.DescriptorPlacement.templateTape M.k) =
      (BitDFT.VectorReady.machine M).tapeOf
        ((BitDFT.VectorReady.machine M).sep :: (y.map (BitDFT.VectorReady.machine M).bitSym ++
          [(BitDFT.VectorReady.machine M).sep])))
    (htHead : c.head (BitDFT.DescriptorPlacement.templateTape M.k) = y.length+1)
    (hx : IntMul.val y+1 ≤ x.length) (out : List Bool)
    (houtput : (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).cells
      (host M).outTape = fun p =>
        encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
          (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p))
    (houtputHead : (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).head
      (host M).outTape = out.length+1) :
    let record := sign::x.take (IntMul.val y+1)
    let First := BitDFT.MachineSequence.native (host M)
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := BitDFT.MachineSequence.sequence
      (BitDFT.RewindTape.control (host M) (sourceTape M)) (control M)
    let q : P.K := Sum.inl (host M).qHalt
    let Post := begin_at_state P Q q
    let Stage := BitDFT.MachineSequence.sequence P Q
    let stageStart := BitDFT.MachineSequence.leftCfg P Q
      (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
        (BitDFT.RecordTerminator.control M)
        (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y))
    ∃ t1 ≤ T+6*(IntMul.val y+1)+4*y.length+7,
      ∃ u ≤ (record.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length + record.length + 7,
      ∃ v ≤ t1+1+u,
        let composed := (BitDFT.MachineSequence.sequence First Post).machine.step^[v]
          (BitDFT.MachineSequence.leftCfg First Post
            ((host M).initCfg input extra))
        composed = BitDFT.MachineSequence.rightCfg First Post
          (to_begin_at_state_cfg P Q q (Stage.machine.step^[u] stageStart)) := by sorry
