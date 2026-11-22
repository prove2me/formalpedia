-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegular_sUnion
-- name    : DeciSigma1.Semantics.isRegular_sUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:17.937361+00:00
-- url     : https://prove2.me/theorems/777f2718-7178-40f2-93ff-7085a11f7fad
-- title:
--   Semantics: is Regular s Union
-- statement:
--   The Semantics construction uses the is Regular s Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L88-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L88-L94

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

theorem DeciSigma1.Semantics.isRegular_sUnion {F : Set (Language n)} (hf : F.Finite) (h : ∀ L ∈ F, IsRegular L) :
    IsRegular (⋃₀ F) := by sorry
