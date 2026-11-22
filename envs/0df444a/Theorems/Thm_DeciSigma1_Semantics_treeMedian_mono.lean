-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_treeMedian_mono
-- name    : DeciSigma1.Semantics.treeMedian_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:26:21.813803+00:00
-- url     : https://prove2.me/theorems/f09b2a27-0e00-40f5-9050-7f981472076a
-- title:
--   Semantics: tree Median mono
-- statement:
--   The Semantics construction uses the tree Median mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L199-L205
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L199-L205

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Data.List.Induction
public import Mathlib.Order.MinMax
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Median
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.treeMedian_mono {a a' b b' c c' : Tree n} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    treeMedian a b c ≤ treeMedian a' b' c' := by sorry
