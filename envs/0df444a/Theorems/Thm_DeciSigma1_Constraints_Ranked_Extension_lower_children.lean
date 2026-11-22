-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_lower_children
-- name    : DeciSigma1.Constraints.Ranked.Extension.lower_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:40.116672+00:00
-- url     : https://prove2.me/theorems/5f6bd27e-d67b-4a46-8bb8-6b2ce911746c
-- title:
--   Extension: lower children
-- statement:
--   The Extension construction uses the lower children property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L105-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L105-L110

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

theorem DeciSigma1.Constraints.Ranked.Extension.lower_children (e : Extension Γ ψ Source Sink rank)
    {a : Fin n → Fin (k + m)} {c : Fin (k + m)} (h : LitT.fLe a c ∈ ψ) (i : Fin n) :
    ¬ Sink (a i) := by sorry
