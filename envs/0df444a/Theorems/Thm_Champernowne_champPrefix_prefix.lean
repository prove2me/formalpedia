-- Prove2me | Theorems.Thm_Champernowne_champPrefix_prefix
-- name    : Champernowne.champPrefix_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:57.782517+00:00
-- url     : https://prove2.me/theorems/d1814474-1ed6-4387-9981-e2c5d0067f46
-- title:
--   Champernowne: champ Prefix prefix
-- statement:
--   `champPrefix b n` is a prefix of the blocks it is carved from.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L48-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L48-L49

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.champPrefix_prefix (b n : ℕ) : champPrefix b n <+: champBlocks b n := by sorry
