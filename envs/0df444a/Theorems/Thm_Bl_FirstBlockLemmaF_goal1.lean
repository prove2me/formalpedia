-- Prove2me | Theorems.Thm_Bl_FirstBlockLemmaF_goal1
-- name    : Bl.FirstBlockLemmaF.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:33.401335+00:00
-- url     : https://prove2.me/theorems/a76e05cd-d1b2-49f1-9e9c-5dbc457606d8
-- title:
--   First Block Lemma F: goal1
-- statement:
--   The First Block Lemma F construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaF/Imports.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaF/Imports.lean#L5-L12

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaF_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaF

theorem Bl.FirstBlockLemmaF.goal1 :
  ∀ (p : Nat) [hp : Fact (Nat.Prime p)] {a b : PadicComplex p} {c : Real},
  LE.le.{0} (Norm.norm.{0} a) c → LE.le.{0} (Norm.norm.{0} b) c → LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b)) c := by sorry
