-- Prove2me | Theorems.Thm_BitDFT_retained_precision
-- name    : BitDFT.retained_precision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:02:08.257062+00:00
-- url     : https://prove2.me/theorems/7d7fad89-93ff-4443-abd7-5d5353e3cf37
-- title:
--   The rewritten input retains precision and dimension on work tapes
-- statement:
--   In the specified final configuration of the input rewriter, suppose its arithmetic word v has value equal to the guard precision q. Work tape 3 contains the canonical binary representation of q with its head immediately after that word. Work tape 4 retains the dimension word with its head immediately after that word. This exposes data available for subsequent charged setup of the output scaler. The actual run to this final configuration is established separately by the input-rewriting theorem.
-- source:
--   Workspace layout needed for the exact Fourier output scaler.

import Definitions.Def_BitDFT_RewriteInput
open BitDFT IntMul

theorem BitDFT.retained_precision (n b : ℕ) (rest v : List Bool)
    (hv : BinaryCounter.value v = guardPrecision n b) :
    (RewriteInput.final n b rest v).cells 3 = RewriteInput.machine.tapeOf
      ((bin (guardPrecision n b).size (guardPrecision n b)).map RewriteInput.machine.bitSym) ∧
    (RewriteInput.final n b rest v).head 3 = (guardPrecision n b).size+1 ∧
    (RewriteInput.final n b rest v).cells 4 = RewriteInput.machine.tapeOf
      ((true :: (bin n.size n).tail).map RewriteInput.machine.bitSym) ∧
    (RewriteInput.final n b rest v).head 4 = (true :: (bin n.size n).tail).length+1 := by sorry
