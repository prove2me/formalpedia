-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_zeroSet
-- name    : BSLambda.LLL.mem_zeroSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:59:34.420939+00:00
-- url     : https://prove2.me/theorems/3f7284ec-b39b-4b0d-8d60-e0f2c5949f0c
-- title:
--   LLL: mem zero Set
-- statement:
--   The LLL construction uses the mem zero Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L223-L225
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L223-L225

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

theorem BSLambda.LLL.mem_zeroSet {x : Input (Construction.Coord ι r)} {i : ι} {k : Fin r} :
    k ∈ zeroSet x i ↔ x (i, k) = false := by sorry
