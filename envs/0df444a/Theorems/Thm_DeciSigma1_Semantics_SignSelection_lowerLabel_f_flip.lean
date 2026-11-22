-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_lowerLabel_f_flip
-- name    : DeciSigma1.Semantics.SignSelection.lowerLabel_f_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:44:40.854054+00:00
-- url     : https://prove2.me/theorems/f3673a58-1e7f-4fbe-90fd-6652087a6767
-- title:
--   Sign Selection: lower Label f flip
-- statement:
--   A constructor supported from below at `u^p` is a constructor supported from above at
--   `u^{1-p}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L117-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L117-L123

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

theorem DeciSigma1.Semantics.SignSelection.lowerLabel_f_flip (hc : FlipClosed ψ) (z : (V × Bool)) (π : List (Fin n)) :
    LowerLabel ψ π .f z ↔ UpperLabel ψ π .f (flipV z) := by sorry
