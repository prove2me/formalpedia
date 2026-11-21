-- Prove2me | Theorems.Thm_Champernowne_champPrefix_eq_map
-- name    : Champernowne.champPrefix_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:29.813665+00:00
-- url     : https://prove2.me/theorems/63bb6de4-8fa4-448a-a01b-54e39534a431
-- title:
--   Champernowne: champ Prefix eq map
-- statement:
--   The Champernowne construction uses the champ Prefix eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Prefix.lean#L49-L59
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Prefix.lean#L49-L59

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Definitions.Def_LeanPool_Champernowne_Prefix
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.champPrefix_eq_map (b n : ℕ) :
    champPrefix b n = (List.range n).map (champDigit b) := by sorry
