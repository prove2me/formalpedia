-- Prove2me | Theorems.Thm_ContinuousLinearMap_rank_zero
-- name    : ContinuousLinearMap.rank_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:44.261831+00:00
-- url     : https://prove2.me/theorems/4a6f1b61-791a-4680-ac90-4cab7414e7b4
-- title:
--   Continuous Linear Map: rank zero
-- statement:
--   The zero map has rank `0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean#L42-L42
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean#L42-L42

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
variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem ContinuousLinearMap.rank_zero : (0 : X →L[𝕜] Y).rank = 0 := by sorry
