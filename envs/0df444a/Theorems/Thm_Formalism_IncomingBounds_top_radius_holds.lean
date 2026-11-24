-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_top_radius_holds
-- name    : Formalism.IncomingBounds.top_radius_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:51.364505+00:00
-- url     : https://prove2.me/theorems/e59b02d5-d846-44a8-9c9a-be60d6f84105
-- title:
--   Incoming Bounds: top radius holds
-- statement:
--   The Incoming Bounds construction uses the top radius holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/AltChooseSumEqZero.lean#L26-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/AltChooseSumEqZero.lean#L26-L86

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_AltChooseSumEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset fwdDiff
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.top_radius_holds : TopRadius := by sorry
