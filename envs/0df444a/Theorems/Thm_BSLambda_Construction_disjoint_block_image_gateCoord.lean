-- Prove2me | Theorems.Thm_BSLambda_Construction_disjoint_block_image_gateCoord
-- name    : BSLambda.Construction.disjoint_block_image_gateCoord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:43.681645+00:00
-- url     : https://prove2.me/theorems/a4633fb6-3fda-4d64-b9ad-4e316d6dca2e
-- title:
--   Construction: disjoint block image gate Coord
-- statement:
--   The owner block `B_i` is disjoint from the outgoing gate coordinates: the gate
--   coordinate of the arc `i → j` lies in the block `B_j`, and `j ≠ i`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L180-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L180-L186

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}

theorem BSLambda.Construction.disjoint_block_image_gateCoord (hT : IsTournament Arc) :
    Disjoint (block i : Finset (Coord ι r)) ((outNbrs Arc i).image (gateCoord γ i)) := by sorry
