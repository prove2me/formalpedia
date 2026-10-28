-- Prove2me | Theorems.Thm_BitDFT_descriptor_slots
-- name    : BitDFT.descriptor_slots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T18:19:24.77747+00:00
-- url     : https://prove2.me/theorems/dcb17c3e-0651-4d34-a342-c66a887642b0
-- title:
--   Exact source and counter tape contents at the routed descriptor setup boundary
-- statement:
--   For child tape count k at least two, the routed setup starts with the binary word y on physical tape k+3, its head just after the word, and blank tapes k+5 and k+6 with heads at their markers. In its specified final configuration, the source is unchanged and both destination tapes contain y between separator symbols, with their heads at the low-order end. The statement identifies complete tape functions, including markers and blank tails, and exact head positions.
-- source:
--   Configuration interface for composing saved precision with the counted coordinate extractor.

import Definitions.Def_BitDFT_DescriptorPlacement
open BitDFT.DescriptorPlacement BitDFT IntMul

theorem BitDFT.descriptor_slots (N : MultitapeTM) (k : ℕ) (hk : 2 ≤ k)
    (cells : Fin (4+(k+3)) → ℕ → N.Sym) (heads : Fin (4+(k+3)) → ℕ)
    (base : RewoundDescriptor.storage.Cfg) (y : List Bool) :
    let start := embed N k cells heads (RewoundDescriptor.initial base y)
    let finish := embed N k cells heads (RewoundDescriptor.final base y)
    start.cells (precisionTape k) = N.tapeOf (y.map N.bitSym) ∧
    start.head (precisionTape k) = y.length+1 ∧
    start.cells (counterTape k) = N.tapeOf [] ∧ start.head (counterTape k) = 0 ∧
    start.cells (templateTape k) = N.tapeOf [] ∧ start.head (templateTape k) = 0 ∧
    finish.cells (precisionTape k) = N.tapeOf (y.map N.bitSym) ∧
    finish.head (precisionTape k) = y.length+1 ∧
    finish.cells (counterTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    finish.head (counterTape k) = y.length+1 ∧
    finish.cells (templateTape k) = N.tapeOf (N.sep :: (y.map N.bitSym ++ [N.sep])) ∧
    finish.head (templateTape k) = y.length+1 := by sorry
