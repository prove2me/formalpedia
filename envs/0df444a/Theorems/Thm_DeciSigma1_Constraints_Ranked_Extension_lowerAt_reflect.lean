-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_lowerAt_reflect
-- name    : DeciSigma1.Constraints.Ranked.Extension.lowerAt_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:57:42.475278+00:00
-- url     : https://prove2.me/theorems/361fe09e-d2ca-4a9c-a9fd-0573cb4e1186
-- title:
--   Extension: lower At reflect
-- statement:
--   A lower path judgment of the extension between original variables holds in the original
--   constraint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L225-L236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L225-L236

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

theorem DeciSigma1.Constraints.Ranked.Extension.lowerAt_reflect (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (h : LowerAt ψ π a b) :
    ∀ u v : Fin k, a = Fin.castAdd m u → b = Fin.castAdd m v → LowerAt Γ π u v := by sorry
