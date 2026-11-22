-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FiniteMedian_median_of_bot
-- name    : DeciSigma1.Semantics.FiniteMedian.median_of_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:04:00.627042+00:00
-- url     : https://prove2.me/theorems/3d6a7151-3804-4bfa-a39b-9fb238185f39
-- title:
--   Finite Median: median of bot
-- statement:
--   The Finite Median construction uses the median of bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L94-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/FiniteMedian.lean#L94-L96

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Median
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.FiniteMedian
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.FiniteMedian.median_of_bot {a b c : FTree n}
    (h : medianSym (rootLabel a) (rootLabel b) (rootLabel c) = .bot) : median a b c = .bot := by sorry
