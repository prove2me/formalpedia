-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_cycleClash_iff
-- name    : DeciSigma1.Constraints.Ranked.Extension.cycleClash_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:11.061378+00:00
-- url     : https://prove2.me/theorems/5e30562d-7f19-444c-bbd9-da0b17543c07
-- title:
--   Extension: cycle Clash iff
-- statement:
--   A ranked extension has a cycle clash exactly when the original constraint has one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L316-L323
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L316-L323

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.Ranked
open DeciSigma1.Constraints.Covariant DeciSigma1.Satisfiability DeciSigma1.Semantics
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}

theorem DeciSigma1.Constraints.Ranked.Extension.cycleClash_iff (e : Extension Γ ψ Source Sink rank) :
    CycleClash ψ ↔ CycleClash Γ := by sorry
