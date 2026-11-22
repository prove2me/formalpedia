-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_SignSelection_mix_fn
-- name    : DeciSigma1.Semantics.SignSelection.mix_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:27:07.115825+00:00
-- url     : https://prove2.me/theorems/3a62c102-0bf8-4546-87de-823a9ee78a07
-- title:
--   Sign Selection: mix fn
-- statement:
--   The Sign Selection construction uses the mix fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L185-L187
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Selector.lean#L185-L187

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

theorem DeciSigma1.Semantics.SignSelection.mix_fn (c : Fin n → Bool) (p : Bool) (a b : Tree n) (h : SameShape a b)
    (π : List (Fin n)) :
    (mix c p a b h).fn π = if Bool.xor p (polarity c π) then b.fn π else a.fn π := by sorry

attribute [defeq] DeciSigma1.Semantics.SignSelection.mix_fn
