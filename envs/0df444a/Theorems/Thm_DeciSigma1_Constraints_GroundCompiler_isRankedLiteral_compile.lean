-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_GroundCompiler_isRankedLiteral_compile
-- name    : DeciSigma1.Constraints.GroundCompiler.isRankedLiteral_compile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:58:29.129+00:00
-- url     : https://prove2.me/theorems/08fe791d-9356-4d48-9f82-da827976b579
-- title:
--   Ground Compiler: is Ranked Literal compile
-- statement:
--   Every compiled literal satisfies `IsRankedLiteral` when the variables of the occurrences lie in
--   `Fresh` and have the rank of `x` plus the depth of their occurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L128-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/GroundBounds.lean#L128-L147

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

theorem DeciSigma1.Constraints.GroundCompiler.isRankedLiteral_compile (lower : Bool) (g : FTree n) (x : V) (e : Occurrence g → V)
    (Fresh : V → Prop) (rank : V → ℕ)
    (hf : ∀ o, Fresh (e o)) (hr : ∀ o, rank (e o) = rank x + depth g o) :
    ∀ l ∈ compile lower x g e, IsRankedLiteral lower Fresh rank l := by sorry
