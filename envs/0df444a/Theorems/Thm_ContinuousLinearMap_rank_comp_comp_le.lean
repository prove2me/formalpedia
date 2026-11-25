-- Prove2me | Theorems.Thm_ContinuousLinearMap_rank_comp_comp_le
-- name    : ContinuousLinearMap.rank_comp_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:49.104739+00:00
-- url     : https://prove2.me/theorems/b220e753-e414-4b6a-ad33-42b9736ffb70
-- title:
--   Continuous Linear Map: rank comp comp le
-- statement:
--   The rank of a composition is bounded by the rank of the middle factor.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean#L63-L76
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean#L63-L76

module
public import Definitions.Def_SNumbers_Basic
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem ContinuousLinearMap.rank_comp_comp_le (A : W →L[𝕜] X) (L : X →L[𝕜] Y) (B : Y →L[𝕜] Z) :
    (B.comp (L.comp A)).rank ≤ L.rank := by sorry
