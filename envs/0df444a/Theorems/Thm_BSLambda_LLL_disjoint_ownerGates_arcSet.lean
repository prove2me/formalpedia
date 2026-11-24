-- Prove2me | Theorems.Thm_BSLambda_LLL_disjoint_ownerGates_arcSet
-- name    : BSLambda.LLL.disjoint_ownerGates_arcSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:33.499635+00:00
-- url     : https://prove2.me/theorems/06971e16-eedb-478e-be03-2d30b8c03e81
-- title:
--   LLL: disjoint owner Gates arc Set
-- statement:
--   The eight conditioned owner gates are disjoint from the arcs among the non-owners.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L907-L911
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L907-L911

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

theorem BSLambda.LLL.disjoint_ownerGates_arcSet (Arc : ι → ι → Bool) (S : Finset ι) (h : ι) :
    Disjoint (ownerGates h (S.erase h)) (arcSet Arc (S.erase h)) := by sorry
