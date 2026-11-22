-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegular_of_closed
-- name    : DeciSigma1.Semantics.isRegular_of_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:25.588276+00:00
-- url     : https://prove2.me/theorems/cb8ae45a-ac60-4446-8044-60ec8ba13a13
-- title:
--   Semantics: is Regular of closed
-- statement:
--   The Semantics construction uses the is Regular of closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L55-L61
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L55-L61

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

theorem DeciSigma1.Semantics.isRegular_of_closed {F : Set (Language n)} (hf : F.Finite) {L : Language n}
    (hl : L ∈ F) (hc : ∀ A ∈ F, ∀ c, residual A [c] ∈ F) : IsRegular L := by sorry
