-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_normalized_decoded
-- name    : DeciSigma1.Constraints.normalized_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:38:40.346743+00:00
-- url     : https://prove2.me/theorems/375623d9-32aa-4d59-894a-f99d92931c59
-- title:
--   Constraints: normalized decoded
-- statement:
--   The Constraints construction uses the normalized decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L152-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L152-L159

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Constraints.normalized_decoded (c : Fin n → Bool) {A : (V × Bool) → Semantics.Tree n}
    (h : Signed.dual A = A) : normalized c (decoded c A) = A := by sorry
