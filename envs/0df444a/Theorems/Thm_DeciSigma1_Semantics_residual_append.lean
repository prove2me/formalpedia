-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_residual_append
-- name    : DeciSigma1.Semantics.residual_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:40:11.879802+00:00
-- url     : https://prove2.me/theorems/36fbf4ce-a26d-489d-afc1-94a4d7fd2f91
-- title:
--   Semantics: residual append
-- statement:
--   The Semantics construction uses the residual append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L51-L53
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L51-L53

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

theorem DeciSigma1.Semantics.residual_append (L : Language n) (u v : List (Fin n)) :
    residual L (u ++ v) = residual (residual L u) v := by sorry
