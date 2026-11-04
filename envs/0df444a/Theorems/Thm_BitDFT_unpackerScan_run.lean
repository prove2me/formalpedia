-- Prove2me | Theorems.Thm_BitDFT_unpackerScan_run
-- name    : BitDFT.unpackerScan_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:58:58.928997+00:00
-- url     : https://prove2.me/theorems/8598918d-7eea-43cb-a24c-55d8479aef2d
-- title:
--   The unary scan consumes $k$ marks in exactly $k$ transitions
-- statement:
--   The unpacking machine reads the unary prefix of its first header by consuming one mark per transition. The theorem says that this scan is exact: starting in the phase that does the scan, with the input tape holding $c_i$ and its head at position $h$, and with the next $k$ cells of the tape all holding marks, after exactly $k$ transitions the machine is still in that phase, the input tape has not changed at all, and the head has advanced by exactly $k$.
--
--   So the machine spends one transition per mark and no more, and it leaves every symbol it has read in place. That is what makes the header parse cost linear in the length of the unary prefix, and it is the induction that every later loop of the machine copies.
--
--   The two conclusions that are *not* in the statement are worth naming. Nothing is claimed about the other five tapes: the phase's rule reads only the symbol under the input head, and the guard's input clause reads only that same cell, so the scan's progress provably does not depend on the rest of the configuration. And nothing is claimed about the counter tape, on which the phase does record a mark per transition; that record is a separate claim, and it is the one whose missing hypothesis — that the counter head has left the end marker — is recorded by `BitDFT.unpackerMachine_counter_blank` and stated by `BitDFT.unpackerSpec_rUnary_step`.
-- source:
--   Internal: run induction for the unary scan of Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachineV2.

import Definitions.Def_BitDFT_unpackerMachineV2

theorem BitDFT.unpackerScan_run (k : ℕ) (c : BitDFT.Unpacker.machine.Cfg) (ci : ℕ → TMKit.Sym)
    (hi : ℕ)
    (h1 : c.state = some ⟨BitDFT.Unpacker.Ph.rUnary, false, false, false⟩)
    (h2 : c.cells BitDFT.Unpacker.machine.inTape = ci)
    (h3 : c.head BitDFT.Unpacker.machine.inTape = hi)
    (hm : ∀ j, j < k → ci (hi + j) = TMKit.Sym.one) :
    (BitDFT.Unpacker.machine.step^[k] c).state
        = some ⟨BitDFT.Unpacker.Ph.rUnary, false, false, false⟩ ∧
      (BitDFT.Unpacker.machine.step^[k] c).cells BitDFT.Unpacker.machine.inTape = ci ∧
      (BitDFT.Unpacker.machine.step^[k] c).head BitDFT.Unpacker.machine.inTape = hi + k := by sorry
