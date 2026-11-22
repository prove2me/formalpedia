-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegular_univ
-- name    : DeciSigma1.Semantics.isRegular_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:16.027721+00:00
-- url     : https://prove2.me/theorems/194aec50-4ce0-4932-afba-e3f303c485c1
-- title:
--   Semantics: is Regular univ
-- statement:
--   The language of all paths is regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L83-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L83-L86

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

theorem DeciSigma1.Semantics.isRegular_univ : IsRegular (Set.univ : Language n) := by sorry
