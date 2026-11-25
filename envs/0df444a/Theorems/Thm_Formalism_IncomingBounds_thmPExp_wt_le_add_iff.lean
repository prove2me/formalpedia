-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_thmPExp_wt_le_add_iff
-- name    : Formalism.IncomingBounds.thmPExp_wt_le_add_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:00.139797+00:00
-- url     : https://prove2.me/theorems/05f30115-71fc-4590-88af-1cb346b1b51a
-- title:
--   Incoming Bounds: thm PExp wt le add iff
-- statement:
--   The Incoming Bounds construction uses the thm PExp wt le add iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L124-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPExp.lean#L124-L130

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds

theorem Formalism.IncomingBounds.thmPExp_wt_le_add_iff (y : WithTop ℝ) (c w : ℝ) :
    ((c : ℝ) : WithTop ℝ) ≤ y + ((w : ℝ) : WithTop ℝ) ↔ ((c - w : ℝ) : WithTop ℝ) ≤ y := by sorry
