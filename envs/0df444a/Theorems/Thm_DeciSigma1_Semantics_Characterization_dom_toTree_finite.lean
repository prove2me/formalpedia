-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Characterization_dom_toTree_finite
-- name    : DeciSigma1.Semantics.Characterization.dom_toTree_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:00:47.718189+00:00
-- url     : https://prove2.me/theorems/62b939f6-10aa-4e76-898a-6208a9598125
-- title:
--   Characterization: dom to Tree finite
-- statement:
--   The Characterization construction uses the dom to Tree finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L173-L195
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Classes.lean#L173-L195

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

theorem DeciSigma1.Semantics.Characterization.dom_toTree_finite (s : FTree n) : (domain s.toTree).Finite := by sorry
