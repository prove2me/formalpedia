-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_zero
-- name    : Formalism.IncomingBounds.tpjet_jetAt0_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:16.083015+00:00
-- url     : https://prove2.me/theorems/04c9862a-232f-43e4-b853-1b8f73231e91
-- title:
--   Incoming Bounds: tpjet jet At0 zero
-- statement:
--   The Incoming Bounds construction uses the tpjet jet At0 zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPJet.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPJet.lean#L45-L48

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
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
variable {C : Type} [Field C]

theorem Formalism.IncomingBounds.tpjet_jetAt0_zero {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by sorry
