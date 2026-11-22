-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Characterization_subtrees_finite_of_dom_finite
-- name    : DeciSigma1.Semantics.Characterization.subtrees_finite_of_dom_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:56.932112+00:00
-- url     : https://prove2.me/theorems/0156eb30-cc79-4d4b-b790-9f3c51044e37
-- title:
--   Characterization: subtrees finite of dom finite
-- statement:
--   Finite trees are regular.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L209-L215
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L209-L215

module
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.Characterization
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.Characterization.subtrees_finite_of_dom_finite (t : Tree n) (h : (domain t).Finite) :
    (subtrees t).Finite := by sorry
