-- Prove2me | Theorems.Thm_Comp_HideOrRun_mid_eq
-- name    : Comp.HideOrRun.mid_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:50:44.710811+00:00
-- url     : https://prove2.me/theorems/d06d2e04-e68b-4cb3-8620-3841199b3db0
-- title:
--   Hide Or Run: mid eq
-- statement:
--   A middle chain that was run and seen to stop pins the `μX` fixed point exactly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L224-L233
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/HideOrRunQ.lean#L224-L233

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeAlmostFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Definitions.Def_Comp_HideOrRunQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
open Comp.HideOrRun

theorem Comp.HideOrRun.mid_eq (b y c : Finset HR) (m : ℕ) (hiter : (midStep b y)^[m] ∅ = c)
    (hfix : midStep b y c = c) :
    ((game.toCSG game_wf).LFInner ↑b ↑y).lfp = (↑c : Set HR) := by sorry
