-- Prove2me | Theorems.Thm_BitDFT_grouped_then_product_offset
-- name    : BitDFT.grouped_then_product_offset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T05:53:02.046809+00:00
-- url     : https://prove2.me/theorems/9b2334bb-096e-4ba5-be1d-326b2626172d
-- title:
--   Position the multiplier operand and move the product to the output suffix
-- statement:
--   Suppose a unary tape has a start marker followed by $3r+5$ one symbols and a non-one sentinel, a distinct operand tape has a binary suffix of length $L$, and a product tape has a unique rewind marker. A fixed multitape controller rewinds the unary counter, uses grouped marks to position the operand head by $r+1$ cells, rewinds the product tape, and advances the product head across the operand's remaining $L$ bits. It reaches the exact output-suffix frame in at most $6r+p+L+18$ transitions, including controller handoffs, while preserving the full tape contents.
-- source:
--   Machine-level composition of the grouped unary positioning run, rewind_tape_correct, rewind_then_bit_advance_to_offset, and exact controller sequencing. This establishes the head-layout interface to counted serialization; descriptor preparation, multiplier invocation, sign restoration, and the full coordinate loop remain separate obligations.

import Definitions.Def_BitDFT_GroupedUnaryAdvance
import Definitions.Def_BitDFT_LiftController
import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_BitAdvance
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_BitAdvance_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic
open IntMul BitDFT.MachineSequence

theorem BitDFT.grouped_then_product_offset
    (N : MultitapeTM)
    (unary operand product : Fin N.k)
    (huo : operand ≠ unary) (hup : unary ≠ product) (hop : operand ≠ product)
    (base : N.Cfg) (r operandHead p L : ℕ)
    (hoperandhead : base.head operand = operandHead)
    (hproducthead : base.head product = p)
    (hmarkerU : base.cells unary 0 = N.startSym)
    (hsourceU : ∀ j, 0 < j → base.cells unary j ≠ N.startSym)
    (hmarks : ∀ j, j < 3*r+5 → base.cells unary (1+j) = N.one)
    (hmarkStop : base.cells unary (1+3*r+5) ≠ N.one)
    (hmarkerP : base.cells product 0 = N.startSym)
    (hsourceP : ∀ j, 0 < j → base.cells product j ≠ N.startSym)
    (hbits : ∀ j, j < L →
      base.cells operand (operandHead+r+1+j) = N.zero ∨
      base.cells operand (operandHead+r+1+j) = N.one)
    (hbitStop : base.cells operand (operandHead+r+1+L) ≠ N.zero ∧
      base.cells operand (operandHead+r+1+L) ≠ N.one) :
    let P := BitDFT.RewindTape.control N unary
    let Q := BitDFT.GroupedUnaryAdvance.control N operand unary huo
    let S := BitDFT.MachineSequence.sequence P Q
    let c₀ := BitDFT.RewindTape.frame N unary base false (3*r+5)
    let cS : S.machine.Cfg := rightCfg P Q
      (BitDFT.GroupedUnaryAdvance.frame N operand unary huo base .halt
        (operandHead+r+1) (1+3*r+5))
    let R := BitDFT.RewindTape.control S.machine product
    let U := BitDFT.BitAdvance.control S.machine product operand (Ne.symm hop)
    let V := BitDFT.MachineSequence.sequence R U
  let Vflat := BitDFT.MachineSequence.liftController S V
    let Vflat := BitDFT.MachineSequence.liftController S V
    ∃ t ≤ (6*r+14)+(p+L+3)+1,
      (BitDFT.MachineSequence.sequence S Vflat).machine.step^[t]
        (leftCfg S Vflat (leftCfg P Q c₀)) =
      rightCfg S Vflat
        (rightCfg R U
          (BitDFT.BitAdvance.frame S.machine product operand (Ne.symm hop)
            cS true (L+1) (operandHead+r+1+L))) := by sorry
