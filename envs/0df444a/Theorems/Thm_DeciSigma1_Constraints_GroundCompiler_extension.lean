-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extension
-- name    : DeciSigma1.Constraints.GroundCompiler.extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:29.368589+00:00
-- url     : https://prove2.me/theorems/45f42ff6-1cbc-4946-a95c-f3f00f15ef58
-- title:
--   Ground Compiler: extension
-- statement:
--   Adding the compiled literals of a ground bound to a constraint `Γ` gives a ranked extension
--   of `Γ`: the fresh variables are sources for a lower bound and sinks for an upper bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L181-L221
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L181-L221

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.GroundCompiler
open DeciSigma1.Semantics
variable {n k : ℕ} {V : Type*}

theorem DeciSigma1.Constraints.GroundCompiler.extension (lower : Bool) (g : FTree n) (x : Fin k) (Γ : List (LitT n (Fin k))) :
    Ranked.Extension Γ (lift Γ _ ++ compile lower (Fin.castAdd _ x) g (occurrenceVar g))
      (fun z => lower = true ∧ k ≤ z.val) (fun z => lower = false ∧ k ≤ z.val) (rank g) := by sorry
