-- Prove2me | Theorems.Thm_Bl_FirstBlockLemmaD_goal1
-- name    : Bl.FirstBlockLemmaD.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:45.656275+00:00
-- url     : https://prove2.me/theorems/5c533532-88e6-4c37-8d32-d294383238cf
-- title:
--   First Block Lemma D: goal1
-- statement:
--   The First Block Lemma D construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaD/Imports.lean#L5-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaD/Imports.lean#L5-L11

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaD

theorem Bl.FirstBlockLemmaD.goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] (x y : PadicAlgCl p),
  LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} x y)) (Max.max.{0} (Norm.norm.{0} x) (Norm.norm.{0} y)) := by sorry
