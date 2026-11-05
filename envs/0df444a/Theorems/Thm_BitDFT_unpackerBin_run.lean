-- Prove2me | Theorems.Thm_BitDFT_unpackerBin_run
-- name    : BitDFT.unpackerBin_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:50:13.482146+00:00
-- url     : https://prove2.me/theorems/f41b6fc3-ae51-48b3-a1b4-ec15c8448db1
-- title:
--   The countdown spends $k$ marks in exactly $k$ transitions
-- statement:
--   The countdown phase of the unpacking machine spends one recorded mark per transition while advancing along the binary digits of $r$. The theorem says the countdown is exact: if the counter holds a mark at each of the cells $h_c, h_c-1, \dots, h_c-k+1$ and $k < h_c$, then after exactly $k$ transitions the phase is unchanged, the input tape is untouched and its head has advanced by $k$, and the counter tape is exactly the counter with those $k$ cells blanked — its head having stepped back by $k$.
--
--   So the machine spends one transition per mark, no more and no fewer, and the recorded count is consumed completely and in place. That is what makes the header parse cost exactly the binary length of $r$, and it is the second of the machine's loop lemmas, after the unary scan.
--
--   The hypothesis that the input tape never holds the end marker is not an artefact: it is what lets each transition pass the input symbol through unchanged, and it holds on the input tape past cell $0$. The hypothesis $k < h_c$ keeps the countdown inside the recorded marks; the transition that meets an empty counter is the phase's separate exit branch.
-- source:
--   Internal: run induction for the binary-digit countdown of Prove2me's BitDFT.unpacking_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98), against the machine definition BitDFT_unpackerMachineV4.

import Definitions.Def_BitDFT_unpackerMachineV4

theorem BitDFT.unpackerBin_run (k : ℕ) (c : BitDFT.Unpacker.machine.Cfg) (ci cc : ℕ → TMKit.Sym)
    (hi hc : ℕ)
    (h1 : c.state = some ⟨BitDFT.Unpacker.Ph.rBinary, false, false, false⟩)
    (h2 : c.cells BitDFT.Unpacker.machine.inTape = ci)
    (h3 : c.head BitDFT.Unpacker.machine.inTape = hi)
    (h4 : c.cells (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ :
      Fin BitDFT.Unpacker.machine.k) = cc)
    (h5 : c.head (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ :
      Fin BitDFT.Unpacker.machine.k) = hc)
    (hin : ∀ p, ci p ≠ TMKit.Sym.start) (hk : k < hc)
    (hm : ∀ j, j < k → cc (hc - j) = TMKit.Sym.one) :
    (BitDFT.Unpacker.machine.step^[k] c).state
        = some ⟨BitDFT.Unpacker.Ph.rBinary, false, false, false⟩ ∧
      (BitDFT.Unpacker.machine.step^[k] c).cells BitDFT.Unpacker.machine.inTape = ci ∧
      (BitDFT.Unpacker.machine.step^[k] c).head BitDFT.Unpacker.machine.inTape = hi + k ∧
      (BitDFT.Unpacker.machine.step^[k] c).cells
          (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k)
        = (fun p => if hc - k < p ∧ p ≤ hc then TMKit.Sym.blank else cc p) ∧
      (BitDFT.Unpacker.machine.step^[k] c).head
          (⟨5, by delta BitDFT.Unpacker.machine; norm_num⟩ : Fin BitDFT.Unpacker.machine.k)
        = hc - k := by sorry
