-- Prove2me | Theorems.Thm_BitDFT_bank_head_setup_correct
-- name    : BitDFT.bank_head_setup_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:20:37.38043+00:00
-- url     : https://prove2.me/theorems/fc740b03-7fc2-4bb0-812a-920786ac717b
-- title:
--   Position all reserved child-bank heads in one transition without changing cells
-- statement:
--   From any configuration, one transition gives the specified final configuration with identical tape contents. Every selected child-bank head initially at zero ends at one. The native input and output heads stay at their original positions. The number of reserved banks is a fixed machine parameter.
-- source:
--   The actual head movement needed to satisfy the tracked caller’s positive bank offsets; no free placement is assumed.

import Definitions.Def_BitDFT_BankHeadSetup
open BitDFT.BankHeadSetup IntMul

theorem BitDFT.bank_head_setup_correct (N : MultitapeTM) (r : ℕ) (base : N.Cfg) :
    (machine N r).step (start N r base) = finish N r base ∧
    (finish N r base).cells = base.cells ∧
    (∀ i : Fin N.k, 2 ≤ i.val → i.val < r+2 → base.head i = 0 → (finish N r base).head i = 1) ∧
    (finish N r base).head N.inTape = base.head N.inTape ∧
    (finish N r base).head N.outTape = base.head N.outTape := by sorry
