-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_baseTerm_le_topTerm
-- name    : Formalism.IncomingBounds.baseTerm_le_topTerm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:41.647209+00:00
-- url     : https://prove2.me/theorems/0ddb533e-7e9d-4e97-966e-9c6e70f8c7b8
-- title:
--   Incoming Bounds: base Term le top Term
-- statement:
--   The Incoming Bounds construction uses the base Term le top Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/BaseTermLeTopTerm.lean#L26-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/BaseTermLeTopTerm.lean#L26-L80

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

theorem Formalism.IncomingBounds.baseTerm_le_topTerm (l d : ℕ) [NeZero d] (hl : 3 ≤ l) (TT : Finset (ZMod d))
    (nu1 nu2 : ZMod d → ℕ) (s : ZMod d) :
    baseTerm l d TT nu1 nu2 s ≤ topTerm l d TT nu1 nu2 s := by sorry
