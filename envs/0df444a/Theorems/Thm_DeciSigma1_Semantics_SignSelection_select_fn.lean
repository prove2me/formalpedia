-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_fn
-- name    : DeciSigma1.Semantics.SignSelection.select_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:35.17741+00:00
-- url     : https://prove2.me/theorems/68426374-ca0e-48b9-857e-39064b8ab36e
-- title:
--   Sign Selection: select fn
-- statement:
--   The Sign Selection construction uses the select fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L260-L263
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L260-L263

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

theorem DeciSigma1.Semantics.SignSelection.select_fn (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) (z : (V × Bool)) (π : List (Fin n)) :
    (select c B h z).fn π =
      if Bool.xor (sign z) (polarity c π) then (dual B z).fn π else (B z).fn π := by sorry
