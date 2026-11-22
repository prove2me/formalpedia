-- Prove2me | Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_mono
-- name    : DeciSigma1.Satisfiability.shapeLabel_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:23:01.012515+00:00
-- url     : https://prove2.me/theorems/bdc970cd-4cf3-46ae-a6b6-017f5369aa0b
-- title:
--   Satisfiability: shape Label mono
-- statement:
--   The shape label is monotone: if support of `f` from below passes from `x` at `π` to `y` at `τ`
--   and support from above passes back, the label of `x` at `π` is at most that of `y` at `τ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L162-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Satisfiability/Shape.lean#L162-L172

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}

theorem DeciSigma1.Satisfiability.shapeLabel_mono {π τ : List (Fin n)} {x y : V}
    (hl : LowerLabel Γ π .f x → LowerLabel Γ τ .f y)
    (hu : ∀ g, UpperLabel Γ τ g y → UpperLabel Γ π g x) :
    shapeLabel Γ x π ≤ shapeLabel Γ y τ := by sorry
