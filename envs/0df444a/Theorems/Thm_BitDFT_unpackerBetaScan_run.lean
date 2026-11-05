-- Prove2me | Theorems.Thm_BitDFT_unpackerBetaScan_run
-- name    : BitDFT.unpackerBetaScan_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T09:37:43.947825+00:00
-- url     : https://prove2.me/theorems/e3de6dd0-0900-40d6-ba58-9a9d0054ca14
-- title:
--   The β-header scan consumes $k$ marks in exactly $k$ transitions
-- statement:
--   The unpacking machine reads the unary prefix of its second header — the bit length of $\beta$, written in unary — by consuming one mark per transition and recording each on a second counter tape. The theorem says that this scan is exact: from the phase that does it, with the input tape holding $c_i$, its head at $h$, and the next $k$ cells all marks, after exactly $k$ transitions the phase is unchanged, the input tape is untouched, and the head has advanced by exactly $k$.
--
--   So the second header costs one transition per unary mark and no more. Together with the corresponding statement about the first header, both header costs are linear in the lengths of their unary prefixes, which is what the machine's overall runtime bound needs.
--
--   The statement mentions no tape other than the input. That is deliberate and true: the phase's rule reads only the symbol under the input head, and the machine's guard on the input tape reads only that same cell, so neither the phase's progress nor the symbols it leaves behind depend on the rest of the configuration. What the phase does to its counter tape is a separate claim.
--
--   This is the same three-part shape as the first header's scan — a per-phase rule, a frame preserved by it, and the induction over the number of marks — applied to `BitDFT_unpackerMachineV4`.
-- source:
--   Internal: run induction for the second header scan of Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachineV4.

import Definitions.Def_BitDFT_unpackerMachineV4

theorem BitDFT.unpackerBetaScan_run (k : ℕ) (c : BitDFT.Unpacker.machine.Cfg)
    (ci : ℕ → TMKit.Sym) (hi : ℕ)
    (h1 : c.state = some ⟨BitDFT.Unpacker.Ph.betaUnary, false, false, false⟩)
    (h2 : c.cells BitDFT.Unpacker.machine.inTape = ci)
    (h3 : c.head BitDFT.Unpacker.machine.inTape = hi)
    (hm : ∀ j, j < k → ci (hi + j) = TMKit.Sym.one) :
    (BitDFT.Unpacker.machine.step^[k] c).state
        = some ⟨BitDFT.Unpacker.Ph.betaUnary, false, false, false⟩ ∧
      (BitDFT.Unpacker.machine.step^[k] c).cells BitDFT.Unpacker.machine.inTape = ci ∧
      (BitDFT.Unpacker.machine.step^[k] c).head BitDFT.Unpacker.machine.inTape = hi + k := by sorry
