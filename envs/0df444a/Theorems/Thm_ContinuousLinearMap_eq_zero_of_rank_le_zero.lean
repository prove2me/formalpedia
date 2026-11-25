-- Prove2me | Theorems.Thm_ContinuousLinearMap_eq_zero_of_rank_le_zero
-- name    : ContinuousLinearMap.eq_zero_of_rank_le_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:53:08.807883+00:00
-- url     : https://prove2.me/theorems/c9a44658-f513-43e1-b9c8-ef2d65ae7de7
-- title:
--   Continuous Linear Map: eq zero of rank le zero
-- statement:
--   The only continuous linear map of rank `0` is the zero map.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean#L45-L49
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/ContinuousLinearMapRank.lean#L45-L49

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

theorem ContinuousLinearMap.eq_zero_of_rank_le_zero {L : X →L[𝕜] Y}
    (hL : L.rank ≤ (0 : Cardinal)) : L = 0 := by sorry
