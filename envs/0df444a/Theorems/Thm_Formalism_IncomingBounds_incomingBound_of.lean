-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_incomingBound_of
-- name    : Formalism.IncomingBounds.incomingBound_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:47.152683+00:00
-- url     : https://prove2.me/theorems/e4eeb444-8244-4902-8992-6ab530510ad1
-- title:
--   Incoming Bounds: incoming Bound of
-- statement:
--   The Incoming Bounds construction uses the incoming Bound of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L203-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaFd.lean#L203-L230

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
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
open Formalism Formalism.IncomingBounds
open FlowDualityReindexing

theorem Formalism.IncomingBounds.incomingBound_of (hF : FlowAttained) (hA : LemmaFa) : IncomingBound := by sorry
