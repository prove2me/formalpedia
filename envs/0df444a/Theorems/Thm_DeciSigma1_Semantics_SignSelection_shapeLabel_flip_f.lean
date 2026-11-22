-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_shapeLabel_flip_f
-- name    : DeciSigma1.Semantics.SignSelection.shapeLabel_flip_f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:31.319912+00:00
-- url     : https://prove2.me/theorems/f2a704e2-4080-4ddb-811e-33665b244c2c
-- title:
--   Sign Selection: shape Label flip f
-- statement:
--   The constructor label of the least shape is invariant under the sign involution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L132-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L132-L141

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

theorem DeciSigma1.Semantics.SignSelection.shapeLabel_flip_f (hc : FlipClosed ψ) (z : (V × Bool)) (π : List (Fin n)) :
    shapeLabel ψ z π = .f ↔ shapeLabel ψ (flipV z) π = .f := by sorry
