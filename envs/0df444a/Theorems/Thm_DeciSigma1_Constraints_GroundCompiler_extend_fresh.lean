-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extend_fresh
-- name    : DeciSigma1.Constraints.GroundCompiler.extend_fresh
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:16.319775+00:00
-- url     : https://prove2.me/theorems/f55e98c9-b399-416d-9754-ee006f3f79bd
-- title:
--   Ground Compiler: extend fresh
-- statement:
--   The Ground Compiler construction uses the extend fresh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L164-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L164-L165

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

theorem DeciSigma1.Constraints.GroundCompiler.extend_fresh (g : FTree n) (ρ : Fin k → Tree n) (o : Occurrence g) :
    extend g ρ (occurrenceVar g o) = (value g o).toTree := by sorry
