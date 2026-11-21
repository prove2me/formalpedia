-- Prove2me | Theorems.Thm_Corless_getD_step_right
-- name    : Corless.getD_step_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:05.235669+00:00
-- url     : https://prove2.me/theorems/70744483-8066-4c79-9b1f-56c4be0468f0
-- title:
--   Corless: get D step right
-- statement:
--   The Corless construction uses the get D step right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L93-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L93-L99

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

theorem Corless.getD_step_right (u : List ℂ) (a b : ℂ) {i : ℕ} (hi : i < u.length) :
    (foldVector u a b).getD (2 * u.length + 1 - i) 1 = u.getD i 1 := by sorry
