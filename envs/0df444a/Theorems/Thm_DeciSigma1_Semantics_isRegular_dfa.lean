-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_isRegular_dfa
-- name    : DeciSigma1.Semantics.isRegular_dfa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:17.912682+00:00
-- url     : https://prove2.me/theorems/2de09506-2d2b-4dc4-addc-56b6212b9ad1
-- title:
--   Semantics: is Regular dfa
-- statement:
--   A language recognized by a finite automaton is regular: its residuals are determined by the
--   reached states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L65-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L65-L69

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

theorem DeciSigma1.Semantics.isRegular_dfa {S : Type*} [Finite S] (M : Semiautomaton (Fin n) S) (F : Set S) :
    IsRegular {w | M.run w ∈ F} := by sorry
