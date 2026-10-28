-- Prove2me | Theorems.Thm_BitDFT_signed_block_initial_match
-- name    : BitDFT.signed_block_initial_match
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:55:27.297227+00:00
-- url     : https://prove2.me/theorems/cfa877d0-ea64-4fa0-869d-bb5c31305e25
-- title:
--   Reconstruct the signed extractor starting configuration from physical tape facts
-- statement:
--   A starting-state configuration with the stated native input, unread signed vector suffix, scratch prefix, and initialized counter and template tapes equals the embedded signed-block starting frame. The conditions include every participating tape head. All other tapes are supplied by the actual configuration itself. This allows the extraction trace to be applied after a concrete preparation phase without assuming uncharged tape copying or head resets.
-- source:
--   Configuration bridge for saved precision and fresh descriptor tapes in the exact DFT output scaler.

import Definitions.Def_BitDFT_SignedBlockPlacement
open BitDFT.SignedBlockPlacement BitDFT IntMul

theorem BitDFT.signed_block_initial_match (N : MultitapeTM) (k : ℕ) (d : (machine N k).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool)
    (hs : d.state = (machine N k).qStart)
    (hroot : d.cells ⟨0,by change 0 < 5+(k+3); omega⟩ = fun p => PreprocessorAlphabet.encode N (rootCells p))
    (hrootHead : d.head ⟨0,by change 0 < 5+(k+3); omega⟩ = rootHead)
    (hv : d.cells ⟨1,by change 1 < 5+(k+3); omega⟩ = N.tapeOf ((pre++sign::x).map N.bitSym))
    (hvHead : d.head ⟨1,by change 1 < 5+(k+3); omega⟩ = pre.length+1)
    (ho : d.cells (scratchTape k) = N.tapeOf (out.map N.bitSym))
    (hoHead : d.head (scratchTape k) = out.length+1)
    (hc : d.cells (counterTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])))
    (hcHead : d.head (counterTape k) = y.length+1)
    (ht : d.cells (templateTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])))
    (htHead : d.head (templateTape k) = y.length+1) :
    embed N k d.cells d.head (WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.initial pre out sign x y)) = d := by sorry
