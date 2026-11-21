-- Prove2me | Theorems.Thm_Corless_mem_vecs
-- name    : Corless.mem_vecs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:31.266626+00:00
-- url     : https://prove2.me/theorems/1082c079-77b7-4193-abe5-51b7dee3e60d
-- title:
--   Corless: mem vecs
-- statement:
--   The Corless construction uses the mem vecs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L243-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L243-L264

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

theorem Corless.mem_vecs (k : ℕ) : ∀ {u : List ℂ}, u ∈ vecs k ↔ CorlessVec k u := by sorry
