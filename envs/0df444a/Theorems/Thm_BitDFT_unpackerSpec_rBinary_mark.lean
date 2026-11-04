-- Prove2me | Theorems.Thm_BitDFT_unpackerSpec_rBinary_mark
-- name    : BitDFT.unpackerSpec_rBinary_mark
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:01:36.505754+00:00
-- url     : https://prove2.me/theorems/bc746381-7ddd-4c01-ae88-02772c25b33e
-- title:
--   The countdown phase: one mark is erased, the counter head steps back, the input advances
-- statement:
--   After the unary prefix of $r$ has been counted, the machine steps past its terminating $0$ and hands over to a phase that consumes that count while advancing along the binary digits of $r$. This theorem records what one transition of that phase does when a mark remains on the counter.
--
--   Three things happen and nothing else. The phase does not change, so the countdown continues. The counter tape's mark is erased — the head is left on a blank, which is how the count is decremented in place — and the counter head steps one cell left. The input tape's symbol is kept and the input head steps one cell right, so the binary digits of $r$ are read off in order.
--
--   The phase's other branch, taken when the counter holds no mark, hands over to the next phase; it is stated separately. Together the two rules make the countdown cost exactly one transition per recorded mark, which is the count of the binary length of $r$.
--
--   This is a theorem about `BitDFT_unpackerMachineV3`. The predecessor versions could not reach this phase at all: the second consumed no marks and the third never left its skip phase, as recorded by `BitDFT.unpackerMachine_counter_blank` and `BitDFT.unpackerSkip_stays`.
-- source:
--   Internal: per-phase transition rule for the binary-digit countdown of Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachineV3.

import Definitions.Def_BitDFT_unpackerMachineV3

theorem BitDFT.unpackerSpec_rBinary_mark (g κ s : Bool) (a : Fin 6 → TMKit.Sym)
    (h : a BitDFT.Unpacker.cntR = TMKit.Sym.one) :
    (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.rBinary, g, κ, s⟩ a).1
        = ⟨BitDFT.Unpacker.Ph.rBinary, g, κ, s⟩ ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.rBinary, g, κ, s⟩ a).2
          BitDFT.Unpacker.cntR = (TMKit.Sym.blank, IntMul.Move.left) ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.rBinary, g, κ, s⟩ a).2
          BitDFT.Unpacker.inT = (a BitDFT.Unpacker.inT, IntMul.Move.right) := by sorry
