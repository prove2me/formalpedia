-- Prove2me | Theorems.Thm_Corless_ext_getD
-- name    : Corless.ext_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:24.886444+00:00
-- url     : https://prove2.me/theorems/44170411-9b21-4493-9165-bc77aac68f76
-- title:
--   Corless: ext get D
-- statement:
--   The Corless construction uses the ext get D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L162-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L162-L167

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless

theorem Corless.ext_getD {l l' : List ℂ} (hl : l.length = l'.length)
    (h : ∀ i < l.length, l.getD i 1 = l'.getD i 1) : l = l' := by sorry
