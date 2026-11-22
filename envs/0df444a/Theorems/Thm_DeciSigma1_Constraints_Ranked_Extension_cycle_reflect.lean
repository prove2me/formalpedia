-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_cycle_reflect
-- name    : DeciSigma1.Constraints.Ranked.Extension.cycle_reflect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:02.21024+00:00
-- url     : https://prove2.me/theorems/ec88cc8e-dfcc-4f92-8eb5-a65f1c50ab4b
-- title:
--   Extension: cycle reflect
-- statement:
--   A cycle clash of the extension along a path `π` gives a cycle clash of the original
--   constraint along `π`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L284-L290
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/RankedExtensions.lean#L284-L290

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

theorem DeciSigma1.Constraints.Ranked.Extension.cycle_reflect (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (hn : π ≠ []) (hl : LowerAt ψ π a a)
    (hd : Derives ψ a b) (hu : UpperAt ψ π b b) :
    ∃ u v : Fin k, LowerAt Γ π u u ∧ Derives Γ u v ∧ UpperAt Γ π v v := by sorry
