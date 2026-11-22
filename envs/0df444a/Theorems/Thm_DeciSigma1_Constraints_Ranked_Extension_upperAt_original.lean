-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_upperAt_original
-- name    : DeciSigma1.Constraints.Ranked.Extension.upperAt_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:59.214571+00:00
-- url     : https://prove2.me/theorems/ca7be939-2a0b-48eb-af1d-a6c685409757
-- title:
--   Extension: upper At original
-- statement:
--   The Extension construction uses the upper At original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L258-L261
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L258-L261

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

theorem DeciSigma1.Constraints.Ranked.Extension.upperAt_original (e : Extension Γ ψ Source Sink rank)
    (π : List (Fin n)) (u v : Fin k) :
    UpperAt ψ π (Fin.castAdd m u) (Fin.castAdd m v) ↔ UpperAt Γ π u v := by sorry
