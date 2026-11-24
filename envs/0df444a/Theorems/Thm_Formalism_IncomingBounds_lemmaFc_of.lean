-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_lemmaFc_of
-- name    : Formalism.IncomingBounds.lemmaFc_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:50.373837+00:00
-- url     : https://prove2.me/theorems/e6d358d9-6e95-4223-8932-1f5a95052a40
-- title:
--   Incoming Bounds: lemma Fc of
-- statement:
--   The Incoming Bounds construction uses the lemma Fc of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaF.lean#L236-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/LemmaF.lean#L236-L259

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaF
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

theorem Formalism.IncomingBounds.lemmaFc_of (hF : FlowAttained) (hA : LemmaFa) : LemmaFc := by sorry
