-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegular_concat
-- name    : DeciSigma1.Semantics.isRegular_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:19.067201+00:00
-- url     : https://prove2.me/theorems/8177f97c-e7b5-4e54-9788-33778eccc520
-- title:
--   Semantics: is Regular concat
-- statement:
--   The concatenation of two regular languages is regular: each residual of `concat A B` is
--   determined by a residual of `A` and a set of residuals of `B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L131-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L131-L159

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

theorem DeciSigma1.Semantics.isRegular_concat {A B : Language n} (ha : IsRegular A) (hb : IsRegular B) :
    IsRegular (concat A B) := by sorry
