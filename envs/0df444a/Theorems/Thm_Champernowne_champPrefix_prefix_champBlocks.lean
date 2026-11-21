-- Prove2me | Theorems.Thm_Champernowne_champPrefix_prefix_champBlocks
-- name    : Champernowne.champPrefix_prefix_champBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:49.326409+00:00
-- url     : https://prove2.me/theorems/2f80dd85-3ccb-4937-8029-839f7b3b5246
-- title:
--   Champernowne: champ Prefix prefix champ Blocks
-- statement:
--   `champPrefix b n` sits inside the complete blocks covering position `n`.
--   This completes the prefix chain `champBlocks (champIndex n) <+: champPrefix n <+:
--   champBlocks (champIndex n + 1)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L204-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L204-L210

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.champPrefix_prefix_champBlocks {b n N : ℕ}
    (h : n ≤ (champBlocks b N).length) :
    champPrefix b n <+: champBlocks b N := by sorry
