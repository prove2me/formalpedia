-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_add
-- name    : Formalism.IncomingBounds.tpjet_jetAt0_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:31:20.184239+00:00
-- url     : https://prove2.me/theorems/bbc71301-d5b3-4036-a5e5-35931000ce01
-- title:
--   Incoming Bounds: tpjet jet At0 add
-- statement:
--   The Incoming Bounds construction uses the tpjet jet At0 add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPJet.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPJet.lean#L27-L43

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

theorem Formalism.IncomingBounds.tpjet_jetAt0_add {σ : Type} (P Q : MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (P + Q) G = jetAt0 P G + jetAt0 Q G := by sorry
