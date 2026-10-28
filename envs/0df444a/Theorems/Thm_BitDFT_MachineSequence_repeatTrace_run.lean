-- Prove2me | Theorems.Thm_BitDFT_MachineSequence_repeatTrace_run
-- name    : BitDFT.MachineSequence.repeatTrace_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T03:15:28.069588+00:00
-- url     : https://prove2.me/theorems/a57a2da4-0079-4bcd-8fdf-5b9356ba8a94
-- title:
--   A trace of repeated body runs is one exact run of the loop machine
-- statement:
--   A finite controller $P$ is wrapped so that it restarts after each body run whenever its read-only source tape is nonblank, and halts at the first blank record boundary. A repeat trace certifies each body run, its first arrival at the exit state, and whether the next source symbol is blank. If the trace has length $t$, then the fixed repeated controller reaches the trace's final configuration in exactly $t$ transitions, counting one loop-control transition after each processed record.
-- source:
--   Machine-level loop execution theorem for the reusable controller BitDFT.MachineSequence.repeatUntilBlank, applied to the repeated scalar-output stage required by BitDFT.rescale_output_machine.

import Definitions.Def_BitDFT_RepeatUntilBlank
set_option autoImplicit false
open BitDFT.MachineSequence IntMul

theorem BitDFT.MachineSequence.repeatTrace_run {M : IntMul.MultitapeTM}
    (P : BitDFT.MachineSequence.Controller M) {t : ℕ}
    {c : P.machine.Cfg} {final : (BitDFT.MachineSequence.repeatMachine P).Cfg}
    (h : BitDFT.MachineSequence.RepeatTrace P t c final) :
    (BitDFT.MachineSequence.repeatMachine P).step^[t]
      (BitDFT.MachineSequence.repeatBodyCfg c) = final := by sorry
