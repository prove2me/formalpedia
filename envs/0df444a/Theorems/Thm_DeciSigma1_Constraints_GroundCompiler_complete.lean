-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_complete
-- name    : DeciSigma1.Constraints.GroundCompiler.complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:55:27.746827+00:00
-- url     : https://prove2.me/theorems/6734ad84-667f-4b88-a0b2-360998654181
-- title:
--   Ground Compiler: complete
-- statement:
--   An assignment that satisfies the bound extends to a solution of the compiled literals.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L168-L172
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L168-L172

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

theorem DeciSigma1.Constraints.GroundCompiler.complete (lower : Bool) (g : FTree n) (x : Fin k) (ρ : Fin k → Tree n)
    (h : if lower then g.toTree ≤ ρ x else ρ x ≤ g.toTree) :
    Covariant.Sat (extend g ρ) (compile lower (Fin.castAdd _ x) g (occurrenceVar g)) := by sorry
