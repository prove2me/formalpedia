-- Prove2me | Theorems.Thm_BitDFT_record_terminator_sequence_step
-- name    : BitDFT.record_terminator_sequence_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:38:00.914756+00:00
-- url     : https://prove2.me/theorems/7786ee60-d520-4dd0-b807-63e7de5f00c5
-- title:
--   Compose extractor handoff with separator insertion
-- statement:
--   Let an extraction machine be halted and let the scratch-head cell be blank. In the composed machine, the next transition hands control to the separator controller and the following transition writes the separator. Thus the complete tape configuration after two transitions is exactly the halted controller state with the separator added, with no head movement.
-- source:
--   The first concrete composition step after extracting the signed Fourier coordinate record.

import Definitions.Def_BitDFT_RecordTerminator
open BitDFT.RecordTerminator BitDFT.MachineSequence IntMul

theorem BitDFT.record_terminator_sequence_step (M : MultitapeTM) (b : (storage M).Cfg)
    (hstate : b.state = (storage M).qHalt)
    (hblank : b.cells (target M) (b.head (target M)) = (storage M).blank) :
    (machine M).step^[2] (leftCfg (native (storage M)) (control M) b) =
      rightCfg (native (storage M)) (control M)
        ⟨true, Function.update b.cells (target M)
          (Function.update (b.cells (target M)) (b.head (target M)) (storage M).sep), b.head⟩ := by sorry
