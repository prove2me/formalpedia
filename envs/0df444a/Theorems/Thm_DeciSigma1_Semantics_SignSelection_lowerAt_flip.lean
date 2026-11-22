-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_lowerAt_flip
-- name    : DeciSigma1.Semantics.SignSelection.lowerAt_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:10.605951+00:00
-- url     : https://prove2.me/theorems/4236b65f-a3fa-4ea6-9e02-45a0592f669c
-- title:
--   Sign Selection: lower At flip
-- statement:
--   On a closed constraint, the sign involution maps lower path judgments to upper ones.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L102-L106
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L102-L106

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}
variable {ψ : List (LitT n (V × Bool))}

theorem DeciSigma1.Semantics.SignSelection.lowerAt_flip (hc : FlipClosed ψ) {π : List (Fin n)} {x y : (V × Bool)}
    (h : LowerAt ψ π x y) : UpperAt ψ π (flipV y) (flipV x) := by sorry
