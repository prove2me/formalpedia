-- Prove2me | Theorems.Thm_Formalism_IncomingBounds_tpjet_jetAt0_superset
-- name    : Formalism.IncomingBounds.tpjet_jetAt0_superset
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:31:44.669792+00:00
-- url     : https://prove2.me/theorems/e52a0baf-1813-451a-b463-a98d3c99810e
-- title:
--   Incoming Bounds: tpjet jet At0 superset
-- statement:
--   The Incoming Bounds construction uses the tpjet jet At0 superset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPJet.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/ThmPJet.lean#L11-L16

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

theorem Formalism.IncomingBounds.tpjet_jetAt0_superset {σ : Type} (P : MvPolynomial σ C) (G : MvPowerSeries σ C)
    (S : Finset (σ →₀ ℕ)) (hS : P.support ⊆ S) :
    jetAt0 P G = ∑ m ∈ S, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m G := by sorry
