-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_extend_original
-- name    : DeciSigma1.Constraints.GroundCompiler.extend_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:53:04.911837+00:00
-- url     : https://prove2.me/theorems/60abe116-b007-4a2b-8b75-b2a4e2d10be8
-- title:
--   Ground Compiler: extend original
-- statement:
--   The Ground Compiler construction uses the extend original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L161-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L161-L162

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

theorem DeciSigma1.Constraints.GroundCompiler.extend_original (g : FTree n) (ρ : Fin k → Tree n) (x : Fin k) :
    extend g ρ (Fin.castAdd _ x) = ρ x := by sorry
