-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_dist_le_hammingDist
-- name    : BSLambda.PartialAssign.dist_le_hammingDist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:28.607051+00:00
-- url     : https://prove2.me/theorems/aaea36bc-907d-4365-b902-f628aa745d2c
-- title:
--   Partial Assign: dist le hamming Dist
-- statement:
--   No point of `C(P)` is closer to `x` than `dist(x, C(P))`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L218-L220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L218-L220

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]

theorem BSLambda.PartialAssign.dist_le_hammingDist {P : PartialAssign V} {x y : Input V} (hy : P.Sat y) :
    P.dist x ≤ hammingDist x y := by sorry
