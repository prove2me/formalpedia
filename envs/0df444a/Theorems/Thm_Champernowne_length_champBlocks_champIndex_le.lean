-- Prove2me | Theorems.Thm_Champernowne_length_champBlocks_champIndex_le
-- name    : Champernowne.length_champBlocks_champIndex_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:54.95344+00:00
-- url     : https://prove2.me/theorems/34561515-ae4a-4bcc-b4e9-eeeac188b6f1
-- title:
--   Champernowne: length champ Blocks champ Index le
-- statement:
--   The Champernowne construction uses the length champ Blocks champ Index le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L32-L36
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L32-L36

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.length_champBlocks_champIndex_le (b n : ℕ) :
    (champBlocks b (champIndex b n)).length ≤ n := by sorry
