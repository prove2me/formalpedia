-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegular_union
-- name    : DeciSigma1.Semantics.isRegular_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:15.574939+00:00
-- url     : https://prove2.me/theorems/40955df1-f8bd-44d4-a461-20fa92e93d50
-- title:
--   Semantics: is Regular union
-- statement:
--   The union of two regular languages is regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L72-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L72-L76

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Automata
variable {n : ℕ}

theorem DeciSigma1.Semantics.isRegular_union {A B : Language n} (ha : IsRegular A) (hb : IsRegular B) :
    IsRegular (A ∪ B) := by sorry
