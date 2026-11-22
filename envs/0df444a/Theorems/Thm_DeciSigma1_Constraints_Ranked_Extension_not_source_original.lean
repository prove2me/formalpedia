-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_source_original
-- name    : DeciSigma1.Constraints.Ranked.Extension.not_source_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:52:39.736828+00:00
-- url     : https://prove2.me/theorems/e8023349-3aaf-414d-b1eb-29eb43658be2
-- title:
--   Extension: not source original
-- statement:
--   The Extension construction uses the not source original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L92-L93
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L92-L93

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

theorem DeciSigma1.Constraints.Ranked.Extension.not_source_original (e : Extension Γ ψ Source Sink rank) (u : Fin k) :
    ¬ Source (Fin.castAdd m u) := by sorry
