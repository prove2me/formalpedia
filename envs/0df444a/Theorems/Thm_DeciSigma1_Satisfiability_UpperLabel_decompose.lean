-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_UpperLabel_decompose
-- name    : DeciSigma1.Satisfiability.UpperLabel.decompose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:24:22.700595+00:00
-- url     : https://prove2.me/theorems/2be4de07-085c-4ab8-b3f7-bd5acf8dbd9d
-- title:
--   Upper Label: decompose
-- statement:
--   Cancel a lower path from an upper label judgment; the dual of `LowerLabel.decompose`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L89-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L89-L99

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.UpperLabel.decompose {π π' : List (Fin n)} {g : Semantics.Sym} {x y : V}
    (h : UpperLabel Γ (π ++ π') g x) (hl : LowerAt Γ π y x) :
    UpperLabel Γ π' g y := by sorry
