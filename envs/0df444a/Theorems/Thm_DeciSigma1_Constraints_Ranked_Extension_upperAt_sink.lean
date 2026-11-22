-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_upperAt_sink
-- name    : DeciSigma1.Constraints.Ranked.Extension.upperAt_sink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:55:15.968267+00:00
-- url     : https://prove2.me/theorems/6abe5f77-682a-4036-8b07-d9a49a508c82
-- title:
--   Extension: upper At sink
-- statement:
--   An upper path judgment starting at a sink ends at a sink of at least the same rank, and of
--   strictly greater rank when the path is nonempty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L206-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L206-L221

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

theorem DeciSigma1.Constraints.Ranked.Extension.upperAt_sink (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (h : UpperAt ψ π a b)
    (ha : Sink a) : Sink b ∧ rank a ≤ rank b ∧ (π ≠ [] → rank a < rank b) := by sorry
