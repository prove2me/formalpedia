-- Prove2me | Theorems.Thm_BSLambda_LLL_arcSet_union_arcSet_swap
-- name    : BSLambda.LLL.arcSet_union_arcSet_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:05:36.008507+00:00
-- url     : https://prove2.me/theorems/77830004-da6c-4a62-a11e-56c6a10952a9
-- title:
--   LLL: arc Set union arc Set swap
-- statement:
--   In a tournament the arcs of `T` and the reversed arcs of `T` together exhaust the
--   off-diagonal pairs of `T`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L123-L130
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L123-L130

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

theorem BSLambda.LLL.arcSet_union_arcSet_swap (T : Finset ι) :
    arcSet Arc T ∪ arcSet (fun a b => Arc b a) T = T.offDiag := by sorry
