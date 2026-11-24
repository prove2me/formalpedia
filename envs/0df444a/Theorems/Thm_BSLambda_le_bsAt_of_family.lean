-- Prove2me | Theorems.Thm_BSLambda_le_bsAt_of_family
-- name    : BSLambda.le_bsAt_of_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:50.192283+00:00
-- url     : https://prove2.me/theorems/720f1991-9ad7-407e-b71b-a30d1233726c
-- title:
--   BSLambda: le bs At of family
-- statement:
--   Exhibiting a family of pairwise disjoint sensitive blocks bounds `bsAt` from below.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L124-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Sensitivity.lean#L124-L126

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]

theorem BSLambda.le_bsAt_of_family [Finite V] {f : Input V → Bool} {x : Input V} {𝓑 : Finset (Finset V)}
    (h : IsBlockFamily f x 𝓑) : 𝓑.card ≤ bsAt f x := by sorry
