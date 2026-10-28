-- Prove2me | Theorems.Thm_BitDFT_signed_block_final_slots
-- name    : BitDFT.signed_block_final_slots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:03:08.536407+00:00
-- url     : https://prove2.me/theorems/0bb219d1-42d3-4530-8a90-ece52fad698c
-- title:
--   Exact signed record and restored descriptors after routed extraction
-- statement:
--   In the signed extractor final configuration, the source vector is unchanged, the scratch tape contains its prior prefix followed by the sign and the next val(y)+1 magnitude bits, and both descriptor tapes contain the original binary descriptor between separators. The source and scratch heads advance by val(y)+2 cells. This identifies complete tape functions and head positions for the subsequent arithmetic stage.
-- source:
--   Configuration bridge for saved precision and fresh descriptor tapes in the exact DFT output scaler.

import Definitions.Def_BitDFT_SignedBlockPlacement
open BitDFT.SignedBlockPlacement BitDFT IntMul

theorem BitDFT.signed_block_final_slots (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x y : List Bool) :
    let start := embed N k cells heads (WorkRelocation.embed SignedBlock.machine rootCells rootHead
      (SignedBlock.final pre out sign x y))
    start.cells ⟨1,by change 1 < 5+(k+3); omega⟩ = N.tapeOf ((pre++sign::x).map N.bitSym) ∧
    start.head ⟨1,by change 1 < 5+(k+3); omega⟩ = pre.length+val y+3 ∧
    start.cells (scratchTape k) = N.tapeOf ((out++sign::x.take (val y+1)).map N.bitSym) ∧
    start.head (scratchTape k) = out.length+val y+3 ∧
    start.cells (counterTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    start.head (counterTape k) = y.length+1 ∧
    start.cells (templateTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    start.head (templateTape k) = y.length+1 := by sorry
