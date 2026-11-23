-- Prove2me | Theorems.Thm_FRI_distance_star_le_relDistanceToSet
-- name    : FRI_distance_star_le_relDistanceToSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:14:26.332593+00:00
-- url     : https://prove2.me/theorems/8f7071a0-622f-4a43-a5fb-54ab4602c44e
-- title:
--   FRI distance star le rel Distance To Set: FRI distance star le rel Distance To Set
-- statement:
--   δ* is at most the distance to the code.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L555-L558
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean#L555-L558

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]

theorem FRI_distance_star_le_relDistanceToSet
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) :
    FRI_distance_star P f_0 bound ≤ relDistanceToSet f_0 (FRI_code P 0).carrier := by sorry
