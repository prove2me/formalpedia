-- Prove2me | Theorems.Thm_BitDFT_repeatTraceOnBounded_runtime
-- name    : BitDFT.repeatTraceOnBounded_runtime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T20:30:12.527419+00:00
-- url     : https://prove2.me/theorems/7c3b9093-f7b1-4592-acf5-436dbc97cdff
-- title:
--   Bound the full runtime of a repeated controller
-- statement:
--   If every nonblank body execution in a repeated-controller trace uses at most B transitions, and the trace has r rounds including the final blank check, then the composed machine reaches the certified final configuration in at most r(B+1) transitions. The result accounts for one loop-control transition per round and preserves the exact run endpoint.
-- source:
--   Finite-controller runtime bridge for the output-rescaling loop. It supplements the exact-run theorem by deriving a total cost from a uniform per-record body bound.

import Definitions.Def_BitDFT_RepeatTraceOnBounded
set_option autoImplicit false
open BitDFT.MachineSequence IntMul

theorem BitDFT.repeatTraceOnBounded_runtime {M : IntMul.MultitapeTM} (source : Fin M.k) (P : BitDFT.MachineSequence.Controller M) (B t : ℕ) (c : P.machine.Cfg) (final : (BitDFT.MachineSequence.repeatMachineOn source P).Cfg) (h : BitDFT.MachineSequence.RepeatTraceOnBounded source P B t c final) : (BitDFT.MachineSequence.repeatMachineOn source P).step^[t] (BitDFT.MachineSequence.repeatBodyCfgOn source c) = final ∧ t ≤ BitDFT.MachineSequence.repeatTraceOnBoundedRounds h * (B + 1) := by sorry
