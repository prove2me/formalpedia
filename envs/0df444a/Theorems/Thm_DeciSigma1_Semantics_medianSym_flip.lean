-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_medianSym_flip
-- name    : DeciSigma1.Semantics.medianSym_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:30:59.762406+00:00
-- url     : https://prove2.me/theorems/eb6fc2ce-340c-4512-8fbb-09274a37dbf2
-- title:
--   Semantics: median Sym flip
-- statement:
--   The Semantics construction uses the median Sym flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L131-L134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L131-L134

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

theorem DeciSigma1.Semantics.medianSym_flip (a b c : Sym) :
    Sym.flip true (medianSym a b c) =
      medianSym (Sym.flip true a) (Sym.flip true b) (Sym.flip true c) := by sorry
