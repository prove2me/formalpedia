-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_upper_children
-- name    : DeciSigma1.Constraints.Ranked.Extension.upper_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:30.966385+00:00
-- url     : https://prove2.me/theorems/fee318aa-2c16-4411-9886-8f711eb52166
-- title:
--   Extension: upper children
-- statement:
--   The Extension construction uses the upper children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L98-L103
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L98-L103

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Ranked
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}

theorem DeciSigma1.Constraints.Ranked.Extension.upper_children (e : Extension Γ ψ Source Sink rank)
    {c : Fin (k + m)} {b : Fin n → Fin (k + m)} (h : LitT.leF c b ∈ ψ) (i : Fin n) :
    ¬ Source (b i) := by sorry
