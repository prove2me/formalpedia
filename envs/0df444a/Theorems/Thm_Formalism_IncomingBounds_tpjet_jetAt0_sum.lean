-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_sum
-- name    : Formalism.IncomingBounds.tpjet_jetAt0_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:10.409742+00:00
-- url     : https://prove2.me/theorems/57810ed6-117c-4cbc-86ff-4c52f596dbe4
-- title:
--   Incoming Bounds: tpjet jet At0 sum
-- statement:
--   The Incoming Bounds construction uses the tpjet jet At0 sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPJet.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPJet.lean#L50-L56

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

theorem Formalism.IncomingBounds.tpjet_jetAt0_sum {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by sorry
