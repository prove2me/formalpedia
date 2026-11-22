-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_signedDual_eq_flipV
-- name    : DeciSigma1.Semantics.SignSelection.signedDual_eq_flipV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:29:17.605581+00:00
-- url     : https://prove2.me/theorems/4fe9c2e5-5483-4d73-8399-a703d54d5f52
-- title:
--   Sign Selection: signed Dual eq flip V
-- statement:
--   The sign dual reads the opposite sign.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L57-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L57-L58

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

theorem DeciSigma1.Semantics.SignSelection.signedDual_eq_flipV (A : (V × Bool) → Tree n) (z : (V × Bool)) :
    dual A z = Tree.dual (A (flipV z)) := by sorry
