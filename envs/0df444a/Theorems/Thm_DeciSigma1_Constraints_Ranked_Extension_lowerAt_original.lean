-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_lowerAt_original
-- name    : DeciSigma1.Constraints.Ranked.Extension.lowerAt_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:57.747482+00:00
-- url     : https://prove2.me/theorems/1d7baec9-7d86-48b6-8567-38727cb72e29
-- title:
--   Extension: lower At original
-- statement:
--   The Extension construction uses the lower At original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L253-L256
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L253-L256

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

theorem DeciSigma1.Constraints.Ranked.Extension.lowerAt_original (e : Extension Γ ψ Source Sink rank)
    (π : List (Fin n)) (u v : Fin k) :
    LowerAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ LowerAt Γ π u v := by sorry
