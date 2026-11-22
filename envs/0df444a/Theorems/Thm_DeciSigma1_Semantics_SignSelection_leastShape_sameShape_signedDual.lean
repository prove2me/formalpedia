-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_leastShape_sameShape_signedDual
-- name    : DeciSigma1.Semantics.SignSelection.leastShape_sameShape_signedDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:29:34.419277+00:00
-- url     : https://prove2.me/theorems/65ddcd12-bb43-4316-831e-ae7fa30db61b
-- title:
--   Sign Selection: least Shape same Shape signed Dual
-- statement:
--   On a constraint closed under the sign involution, the least shape `B` and its sign dual have the
--   same constructor positions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L195-L200
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L195-L200

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

theorem DeciSigma1.Semantics.SignSelection.leastShape_sameShape_signedDual {ψ : List (LitT n (V × Bool))} (hc : FlipClosed ψ)
    (z : (V × Bool)) : SameShape (leastShape ψ z) (dual (leastShape ψ) z) := by sorry
