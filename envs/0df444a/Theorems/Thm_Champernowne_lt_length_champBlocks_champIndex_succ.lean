-- Prove2me | Theorems.Thm_Champernowne_lt_length_champBlocks_champIndex_succ
-- name    : Champernowne.lt_length_champBlocks_champIndex_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:32.901601+00:00
-- url     : https://prove2.me/theorems/0dff40aa-e917-4bcc-bdfc-f0339c81073d
-- title:
--   Champernowne: lt length champ Blocks champ Index succ
-- statement:
--   The Champernowne construction uses the lt length champ Blocks champ Index succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L38-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L38-L45

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.lt_length_champBlocks_champIndex_succ (b n : ℕ) :
    n < (champBlocks b (champIndex b n + 1)).length := by sorry
