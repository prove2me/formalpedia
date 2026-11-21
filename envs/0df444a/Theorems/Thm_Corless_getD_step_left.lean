-- Prove2me | Theorems.Thm_Corless_getD_step_left
-- name    : Corless.getD_step_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:10.763302+00:00
-- url     : https://prove2.me/theorems/4f990506-3be6-4190-885e-05289b05fb78
-- title:
--   Corless: get D step left
-- statement:
--   The Corless construction uses the get D step left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L79-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L79-L81

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

theorem Corless.getD_step_left (u : List ℂ) (a b : ℂ) {i : ℕ} (hi : i < u.length) :
    (foldVector u a b).getD i 1 = u.getD i 1 := by sorry
