-- Prove2me | Theorems.Thm_BitDFT_MachineSequence_repeatTraceOn_run
-- name    : BitDFT.MachineSequence.repeatTraceOn_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T03:27:29.089673+00:00
-- url     : https://prove2.me/theorems/7d88fb2f-36b6-4c39-bbbd-48ab5d854e01
-- title:
--   Exact run of a controller repeated over a designated tape
-- statement:
--   Let a finite controller process records on a designated tape and stop after each record. A finite trace records the exact run taken for each record, including one final blank test. The theorem states that the wrapper which restarts the controller at each record executes the certified trace in exactly the sum of the body-run lengths plus one control step per record.
-- source:
--   Reusable machine-composition lemma for output postprocessing in the integer-multiplication to finite-precision Fourier transfer formalization.

import Definitions.Def_BitDFT_RepeatUntilBlankOn
set_option autoImplicit false

theorem BitDFT.MachineSequence.repeatTraceOn_run {M : IntMul.MultitapeTM}
    (source : Fin M.k) (P : BitDFT.MachineSequence.Controller M) {t : ℕ}
    {c : P.machine.Cfg} {final : (BitDFT.MachineSequence.repeatMachineOn source P).Cfg}
    (h : BitDFT.MachineSequence.RepeatTraceOn source P t c final) :
    (BitDFT.MachineSequence.repeatMachineOn source P).step^[t]
      (BitDFT.MachineSequence.repeatBodyCfgOn source c) = final := by sorry
