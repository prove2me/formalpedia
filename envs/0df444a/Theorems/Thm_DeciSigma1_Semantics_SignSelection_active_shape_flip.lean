-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_active_shape_flip
-- name    : DeciSigma1.Semantics.SignSelection.active_shape_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:29:34.470327+00:00
-- url     : https://prove2.me/theorems/bb761a18-4751-4363-a3cc-a51317fdeda6
-- title:
--   Sign Selection: active shape flip
-- statement:
--   The Sign Selection construction uses the active shape flip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L143-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L143-L145

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

theorem DeciSigma1.Semantics.SignSelection.active_shape_flip (hc : FlipClosed ψ) (z : (V × Bool)) (π : List (Fin n)) :
    IsLivePrefix (shapeLabel ψ z) π ↔ IsLivePrefix (shapeLabel ψ (flipV z)) π := by sorry
