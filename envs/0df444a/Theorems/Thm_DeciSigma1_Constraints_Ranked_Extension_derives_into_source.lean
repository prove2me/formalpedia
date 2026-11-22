-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_into_source
-- name    : DeciSigma1.Constraints.Ranked.Extension.derives_into_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:19.173649+00:00
-- url     : https://prove2.me/theorems/d7a93f2d-24bd-40a2-a688-bea63343e704
-- title:
--   Extension: derives into source
-- statement:
--   A derivation that ends in a source is trivial.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L113-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L113-L123

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

theorem DeciSigma1.Constraints.Ranked.Extension.derives_into_source (e : Extension Γ ψ Source Sink rank)
    {a b : Fin (k + m)} (h : Derives ψ a b) (hb : Source b) : a = b := by sorry
