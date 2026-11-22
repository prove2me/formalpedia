-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_reflect
-- name    : DeciSigma1.Constraints.Ranked.Extension.derives_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:55.213805+00:00
-- url     : https://prove2.me/theorems/621a94ad-2ae5-4443-8b4b-ee693913ba40
-- title:
--   Extension: derives reflect
-- statement:
--   The Extension construction uses the derives reflect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L150-L178
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L150-L178

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

theorem DeciSigma1.Constraints.Ranked.Extension.derives_reflect (e : Extension Γ ψ Source Sink rank)
    {a b : Fin (k + m)} (h : Derives ψ a b) :
    ∀ u v : Fin k, a = Fin.castAdd m u → b = Fin.castAdd m v → Derives Γ u v := by sorry
