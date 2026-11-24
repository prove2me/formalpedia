-- Prove2me | Theorems.Thm_BSLambda_LLL_disjoint_arcSet_arcSet_swap
-- name    : BSLambda.LLL.disjoint_arcSet_arcSet_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:36.626789+00:00
-- url     : https://prove2.me/theorems/78fced8e-c5b9-4fcf-b75f-a7ec94077e27
-- title:
--   LLL: disjoint arc Set arc Set swap
-- statement:
--   A pair cannot carry an arc in both directions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L134-L138
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L134-L138

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
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}
variable (hT : IsTournament Arc)
include hT
omit [DecidableEq ι]

theorem BSLambda.LLL.disjoint_arcSet_arcSet_swap (T : Finset ι) :
    Disjoint (arcSet Arc T) (arcSet (fun a b => Arc b a) T) := by sorry
