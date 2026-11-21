-- Prove2me | Theorems.Thm_Corless_Fam_congr
-- name    : Corless.Fam_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:42:08.038903+00:00
-- url     : https://prove2.me/theorems/4841f0d6-9523-49be-b152-ecace6e6b5b5
-- title:
--   Corless: Fam congr
-- statement:
--   `Fam k s` only depends on the first `2^(k+1) - 2` signs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L58-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CorlessNilpotent/Vectors.lean#L58-L75

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

theorem Corless.Fam_congr : ∀ (k : ℕ) {s t : ℕ → ℤ}, (∀ i < 2 ^ (k + 1) - 2, s i = t i) →
    (Fam k s ↔ Fam k t)
  := by sorry
