-- Prove2me | Theorems.Thm_BSLambda_LLL_intObstruction_one_pattern
-- name    : BSLambda.LLL.intObstruction_one_pattern
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:57.070809+00:00
-- url     : https://prove2.me/theorems/8780c03e-c702-4bb0-849f-6c93f8ceb097
-- title:
--   LLL: int Obstruction one pattern
-- statement:
--   **Section 8**: a radius-one obstruction realises exactly one of the two patterns —
--   either `h` dominates the whole support (Type A), or a single `a` beats `h` and the two of
--   them jointly dominate the rest (Type B).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L645-L672
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L645-L672

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem BSLambda.LLL.intObstruction_one_pattern {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) :
    (∀ j ∈ S, j ≠ h → Arc h j = true) ∨
      ∃ a ∈ S, a ≠ h ∧ Arc a h = true ∧
        ∀ j ∈ S, j ≠ h → j ≠ a → Arc h j = true ∧ Arc a j = true := by sorry
