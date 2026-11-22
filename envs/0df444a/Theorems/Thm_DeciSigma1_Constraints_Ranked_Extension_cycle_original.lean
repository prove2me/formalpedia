-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_cycle_original
-- name    : DeciSigma1.Constraints.Ranked.Extension.cycle_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:04.127848+00:00
-- url     : https://prove2.me/theorems/5a5dcb8a-96cc-4f92-b5e7-5ecb11ab5317
-- title:
--   Extension: cycle original
-- statement:
--   The two variables of a cycle clash of the extension are original variables.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L264-L280
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L264-L280

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

theorem DeciSigma1.Constraints.Ranked.Extension.cycle_original (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    (∃ u : Fin k, a = Fin.castAdd m u) ∧ (∃ v : Fin k, b = Fin.castAdd m v) := by sorry
