-- Prove2me | Theorems.Thm_Corless_CorlessVec_length_eq
-- name    : Corless.CorlessVec.length_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:55.623608+00:00
-- url     : https://prove2.me/theorems/6538217b-0ff1-49fe-99ab-c07f8e239d7c
-- title:
--   Corless Vec: length eq
-- statement:
--   The Corless Vec construction uses the length eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L103-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L103-L109

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

theorem Corless.CorlessVec.length_eq {k : ℕ} {u : List ℂ} (h : CorlessVec k u) :
    u.length = 2 ^ (k + 1) - 2 := by sorry
