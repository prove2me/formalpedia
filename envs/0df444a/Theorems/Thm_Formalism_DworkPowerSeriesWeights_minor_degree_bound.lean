-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_minor_degree_bound
-- name    : Formalism.DworkPowerSeriesWeights.minor_degree_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:25:24.981958+00:00
-- url     : https://prove2.me/theorems/63cd25c5-3835-45f1-b757-4f9ea303f6d0
-- title:
--   Dwork Power Series Weights: minor degree bound
-- statement:
--   The Dwork Power Series Weights construction uses the minor degree bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L410-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L410-L418

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.minor_degree_bound : MinorDeg.{u} := by sorry
