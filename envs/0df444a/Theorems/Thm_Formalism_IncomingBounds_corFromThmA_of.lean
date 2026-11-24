-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_corFromThmA_of
-- name    : Formalism.IncomingBounds.corFromThmA_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:37.513064+00:00
-- url     : https://prove2.me/theorems/c818ef07-7a33-45f2-8900-41aaadf340b7
-- title:
--   Incoming Bounds: cor From Thm A of
-- statement:
--   The Incoming Bounds construction uses the cor From Thm A of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/BaseTermLeTopTerm.lean#L82-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/BaseTermLeTopTerm.lean#L82-L188

import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_BaseTermLeTopTerm
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

theorem Formalism.IncomingBounds.corFromThmA_of (hF : FlowAttained) (hA : LemmaFa) (hc : LemmaFc) (hI : IncomingBound) :
    CorFromThmA := by sorry
