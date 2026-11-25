-- Prove2me | Theorems.Thm_CompanionTheory_RgExh_isSimple_triv
-- name    : CompanionTheory.RgExh.isSimple_triv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:03.974589+00:00
-- url     : https://prove2.me/theorems/bfafb425-ce61-4837-913a-1ea3d32a02f4
-- title:
--   Rg Exh: is Simple triv
-- statement:
--   The Rg Exh construction uses the is Simple triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/IsSimpleTriv.lean#L108-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/IsSimpleTriv.lean#L108-L108

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_IsSimpleTriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open CompanionTheory CompanionTheory.RgExh
open Formalism.REAL (GlRel qdet)
variable {n : ℕ}
attribute [instance] GMod.acg GMod.mod

theorem CompanionTheory.RgExh.isSimple_triv : IsSimple (triv n) := by sorry
