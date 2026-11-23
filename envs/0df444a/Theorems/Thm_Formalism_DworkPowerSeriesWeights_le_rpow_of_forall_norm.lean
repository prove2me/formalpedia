-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_le_rpow_of_forall_norm
-- name    : Formalism.DworkPowerSeriesWeights.le_rpow_of_forall_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:42.630086+00:00
-- url     : https://prove2.me/theorems/6cbec74d-d097-4ce6-bd93-62c9e96adb02
-- title:
--   Dwork Power Series Weights: le rpow of forall norm
-- statement:
--   The Dwork Power Series Weights construction uses the le rpow of forall norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/TheoremAMatrixEntries.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/TheoremAMatrixEntries.lean#L40-L57

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

theorem Formalism.DworkPowerSeriesWeights.le_rpow_of_forall_norm (l : ℕ) [hl : Fact l.Prime] (b x : ℝ) (hx : 0 ≤ x)
    (h : ∀ c : ℂ_[l], ‖(l : ℂ_[l])‖ ^ b ≤ ‖c‖ → x ≤ ‖c‖) : x ≤ ‖(l : ℂ_[l])‖ ^ b := by sorry
