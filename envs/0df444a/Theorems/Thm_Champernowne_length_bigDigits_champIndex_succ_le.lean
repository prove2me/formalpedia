-- Prove2me | Theorems.Thm_Champernowne_length_bigDigits_champIndex_succ_le
-- name    : Champernowne.length_bigDigits_champIndex_succ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:53.538123+00:00
-- url     : https://prove2.me/theorems/c24d7cc6-32e4-429d-85e5-2a91b17e583c
-- title:
--   Champernowne: length big Digits champ Index succ le
-- statement:
--   The straddling number has at most `M + 1` digits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L67-L73
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Positions.lean#L67-L73

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.length_bigDigits_champIndex_succ_le {b n M : ℕ} (hb : 1 < b)
    (h2 : champIndex b n + 1 ≤ b ^ M) :
    (bigDigits b (champIndex b n + 1)).length ≤ M + 1 := by sorry
