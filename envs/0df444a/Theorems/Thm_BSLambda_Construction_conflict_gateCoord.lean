-- Prove2me | Theorems.Thm_BSLambda_Construction_conflict_gateCoord
-- name    : BSLambda.Construction.conflict_gateCoord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:49:22.668005+00:00
-- url     : https://prove2.me/theorems/797c3174-31d6-4a26-a8f2-3673c2663e0a
-- title:
--   Construction: conflict gate Coord
-- statement:
--   If `i → j` then `q_{ij} = (j, γ(i,j))` is a conflicting literal between `C_i`
--   and `C_j` (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L52-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L52-L54

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}

theorem BSLambda.Construction.conflict_gateCoord (hji : j ≠ i) (hij : Arc i j) :
    (cert Arc γ i).Conflict (cert Arc γ j) (gateCoord γ i j) := by sorry
