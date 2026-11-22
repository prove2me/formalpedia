-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_out_of_sink
-- name    : DeciSigma1.Constraints.Ranked.Extension.derives_out_of_sink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:37.197267+00:00
-- url     : https://prove2.me/theorems/e49ea2d8-6172-4cac-b94d-9f78204bfc7d
-- title:
--   Extension: derives out of sink
-- statement:
--   A derivation that starts in a sink is trivial.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L126-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L126-L136

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

theorem DeciSigma1.Constraints.Ranked.Extension.derives_out_of_sink (e : Extension Γ ψ Source Sink rank)
    {a b : Fin (k + m)} (h : Derives ψ a b) (ha : Sink a) : b = a := by sorry
