-- Prove2me | Theorems.Thm_BitDFT_unpackerSpec_betaCopy_mark
-- name    : BitDFT.unpackerSpec_betaCopy_mark
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:51:20.162694+00:00
-- url     : https://prove2.me/theorems/cf83a206-46e4-4285-95f1-fdc6bc4dedf7
-- title:
--   The β-copy phase: one bit crosses from the input to the template
-- statement:
--   The machine carries the binary digits of $\beta$ from the input tape onto a template tape, one digit per recorded mark on the $\beta$ counter. The theorem records one transition of that copy, on a mark.
--
--   Four things happen and nothing else. The phase keeps its name, so the copy continues while marks remain. The counter's mark is erased and its head steps left, which is how the count of remaining digits is decremented in place. The symbol under the input head is copied onto the template tape, whose head steps right, so the digits appear on the template in the order they are read. And the input head steps right, moving to the next digit.
--
--   No other tape is touched. The statement lists the four effects plus the frame condition, which is what the induction over the digits consumes: the phase's rule reads only the counter cell and the input cell, so the copy's progress depends on nothing else.
--
--   The hypotheses are structural. The counter cell holds a mark, so the phase does not take its hand-over branch; and the three tape indices are distinct, so the four effects do not interfere with one another.
-- source:
--   Internal: per-phase transition rule for the β-digit copy of Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachineV6.

import Definitions.Def_BitDFT_unpackerMachineV6

theorem BitDFT.unpackerSpec_betaCopy_mark (g κ s : Bool) (a : Fin 6 → TMKit.Sym)
    (h : a BitDFT.Unpacker.cnt = TMKit.Sym.one) :
    (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).1
        = ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).2
          BitDFT.Unpacker.cnt = (TMKit.Sym.blank, IntMul.Move.left) ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).2
          BitDFT.Unpacker.tpl = (a BitDFT.Unpacker.inT, IntMul.Move.right) ∧
      (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).2
          BitDFT.Unpacker.inT = (a BitDFT.Unpacker.inT, IntMul.Move.right) ∧
      ∀ i, i ≠ BitDFT.Unpacker.cnt → i ≠ BitDFT.Unpacker.tpl → i ≠ BitDFT.Unpacker.inT →
        (BitDFT.Unpacker.spec ⟨BitDFT.Unpacker.Ph.betaCopyGo, g, κ, s⟩ a).2 i
          = (a i, IntMul.Move.stay) := by sorry
