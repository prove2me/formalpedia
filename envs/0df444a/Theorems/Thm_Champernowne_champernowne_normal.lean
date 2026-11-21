-- Prove2me | Theorems.Thm_Champernowne_champernowne_normal
-- name    : Champernowne.champernowne_normal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:39:28.41388+00:00
-- url     : https://prove2.me/theorems/d8f93b4c-9f31-42db-b8b4-61ddfde95e52
-- title:
--   Champernowne: champernowne normal
-- statement:
--   The Champernowne construction uses the champernowne normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Main.lean#L20-L24
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Main.lean#L20-L24

module
public import Definitions.Def_LeanPool_Champernowne_Asymptotics
public import Definitions.Def_LeanPool_Champernowne_Main
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.champernowne_normal (b : ℕ) (hb : 2 ≤ b) :
    IsNormalSequence b (champDigit b) := by sorry
