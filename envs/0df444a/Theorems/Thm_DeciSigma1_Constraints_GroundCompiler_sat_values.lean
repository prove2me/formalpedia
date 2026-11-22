-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_sat_values
-- name    : DeciSigma1.Constraints.GroundCompiler.sat_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:16.199382+00:00
-- url     : https://prove2.me/theorems/60c8089a-2481-4882-b746-c5cb82c3ef82
-- title:
--   Ground Compiler: sat values
-- statement:
--   An assignment that satisfies the bound and gives the variable of each occurrence the subtree
--   at that occurrence satisfies the compiled literals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L98-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L98-L115

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

theorem DeciSigma1.Constraints.GroundCompiler.sat_values (lower : Bool) (g : FTree n) (x : V) (e : Occurrence g → V)
    (ρ : V → Tree n) (he : ∀ o, ρ (e o) = (value g o).toTree)
    (h : if lower then g.toTree ≤ ρ x else ρ x ≤ g.toTree) :
    Covariant.Sat ρ (compile lower x g e) := by sorry
