-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_gValK_algebraMap
-- name    : Formalism.DworkPowerSeriesWeights.gValK_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:24.932999+00:00
-- url     : https://prove2.me/theorems/ca2c372b-eecf-4c46-aec1-0c094c5247f8
-- title:
--   Dwork Power Series Weights: g Val K algebra Map
-- statement:
--   The Dwork Power Series Weights construction uses the g Val K algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/GField.lean#L173-L175

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {F : Type} [NormedField F] {σ : Type}
variable [IsUltrametricDist F]

theorem Formalism.DworkPowerSeriesWeights.gValK_algebraMap (P : MvPolynomial σ F) :
    ((gValK F σ (algebraMap _ (GK F σ) P) : ℝ≥0) : ℝ) = gN P := by sorry
