-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_exists_norm_eq_rpow_rat
-- name    : Formalism.DworkPowerSeriesWeights.exists_norm_eq_rpow_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:23.145855+00:00
-- url     : https://prove2.me/theorems/e7ece425-4b2a-422d-83cd-dca34a0198eb
-- title:
--   Dwork Power Series Weights: exists norm eq rpow rat
-- statement:
--   The Dwork Power Series Weights construction uses the exists norm eq rpow rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/TheoremAMatrixEntries.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/TheoremAMatrixEntries.lean#L23-L38

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

theorem Formalism.DworkPowerSeriesWeights.exists_norm_eq_rpow_rat (l : ℕ) [hl : Fact l.Prime] (q : ℚ) :
    ∃ c : ℂ_[l], ‖c‖ = ‖(l : ℂ_[l])‖ ^ (q : ℝ) := by sorry
