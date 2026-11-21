-- Prove2me | Theorems.Thm_Champernowne_n_lt_length_champIndex_add
-- name    : Champernowne.n_lt_length_champIndex_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:49.091795+00:00
-- url     : https://prove2.me/theorems/6fde9e94-9ebb-42e4-99f6-d2ffbf128220
-- title:
--   Champernowne: n lt length champ Index add
-- statement:
--   Position `n` lies within one number's digits of the complete blocks.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L60-L64
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L60-L64

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.n_lt_length_champIndex_add (b n : ℕ) :
    n < (champBlocks b (champIndex b n)).length
      + (bigDigits b (champIndex b n + 1)).length := by sorry
