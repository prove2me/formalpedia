-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_upperAt_flip
-- name    : DeciSigma1.Semantics.SignSelection.upperAt_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:10.172419+00:00
-- url     : https://prove2.me/theorems/907ffdeb-dbb0-4a59-af27-8a7318bc1ddd
-- title:
--   Sign Selection: upper At flip
-- statement:
--   On a closed constraint, the sign involution maps upper path judgments to lower ones.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L109-L113
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L109-L113

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

theorem DeciSigma1.Semantics.SignSelection.upperAt_flip (hc : FlipClosed ψ) {π : List (Fin n)} {x y : (V × Bool)}
    (h : UpperAt ψ π x y) : LowerAt ψ π (flipV y) (flipV x) := by sorry
