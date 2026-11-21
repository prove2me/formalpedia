-- Prove2me | Theorems.Thm_Corless_CorlessVec_mem
-- name    : Corless.CorlessVec.mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:15.425764+00:00
-- url     : https://prove2.me/theorems/5e1276d8-d301-4f09-859b-45402eb6ad01
-- title:
--   Corless Vec: mem
-- statement:
--   The Corless Vec construction uses the mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L111-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L111-L122

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

theorem Corless.CorlessVec.mem {k : ℕ} {u : List ℂ} (h : CorlessVec k u) :
    ∀ x ∈ u, x = 1 ∨ x = Complex.I := by sorry
