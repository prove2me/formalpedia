-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_lowerAt_source
-- name    : DeciSigma1.Constraints.Ranked.Extension.lowerAt_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:55:08.350197+00:00
-- url     : https://prove2.me/theorems/98562ad1-56fe-44d3-af4a-c4ca391ffd28
-- title:
--   Extension: lower At source
-- statement:
--   A lower path judgment ending at a source starts at a source of at least the same rank, and of
--   strictly greater rank when the path is nonempty.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L187-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L187-L202

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

theorem DeciSigma1.Constraints.Ranked.Extension.lowerAt_source (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (h : LowerAt ψ π a b)
    (hb : Source b) : Source a ∧ rank b ≤ rank a ∧ (π ≠ [] → rank b < rank a) := by sorry
