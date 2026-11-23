-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_one_left
-- name    : Formalism.DworkPowerSeriesWeights.jetPair_one_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:44.319962+00:00
-- url     : https://prove2.me/theorems/24bcacc6-b907-44c6-bba7-b530d3ec75f5
-- title:
--   Dwork Power Series Weights: jet Pair one left
-- statement:
--   The Dwork Power Series Weights construction uses the jet Pair one left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L38-L40

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {K : Type u} [Field K] {ι : Type} [Fintype ι]

theorem Formalism.DworkPowerSeriesWeights.jetPair_one_left (F : MvPowerSeries ι K) :
    jetPair (1 : MvPolynomial ι K) F = MvPowerSeries.constantCoeff F := by sorry
