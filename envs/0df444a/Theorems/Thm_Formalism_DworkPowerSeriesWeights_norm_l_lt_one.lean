-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_l_lt_one
-- name    : Formalism.DworkPowerSeriesWeights.norm_l_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:50.902098+00:00
-- url     : https://prove2.me/theorems/1e03807f-0a21-4742-9e5f-a8ad68c25766
-- title:
--   Dwork Power Series Weights: norm l lt one
-- statement:
--   The Dwork Power Series Weights construction uses the norm l lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/TheoremAMatrixEntries.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/TheoremAMatrixEntries.lean#L15-L21

import Definitions.Def_Formalism_GaussJetBounds_StatementV
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAMatrixEntries
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.norm_l_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by sorry
