-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_sound
-- name    : DeciSigma1.Constraints.GroundCompiler.sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:13.657841+00:00
-- url     : https://prove2.me/theorems/99598f99-4623-4822-bfb7-d3fc3bb584b8
-- title:
--   Ground Compiler: sound
-- statement:
--   Every solution of the compiled literals satisfies the bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L79-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L79-L94

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
public import Theorems.Thm_DeciSigma1_Constraints_Derives_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerF_sound
public import Theorems.Thm_DeciSigma1_Constraints_LowerTop_sound
public import Theorems.Thm_DeciSigma1_Constraints_UpperBot_sound
public import Theorems.Thm_DeciSigma1_Constraints_UpperF_sound

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints DeciSigma1.Constraints.GroundCompiler
open DeciSigma1.Semantics
variable {n k : ℕ} {V : Type*}

theorem DeciSigma1.Constraints.GroundCompiler.sound (lower : Bool) (g : FTree n) (x : V) (e : Occurrence g → V)
    {ρ : V → Tree n} (h : Covariant.Sat ρ (compile lower x g e)) :
    if lower then g.toTree ≤ ρ x else ρ x ≤ g.toTree := by sorry
