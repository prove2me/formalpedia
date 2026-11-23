-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_quadSer
-- name    : Formalism.DworkPowerSeriesWeights.constantCoeff_quadSer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:36.277951+00:00
-- url     : https://prove2.me/theorems/4c7412e8-e570-46a8-b5ee-b63a65d646a0
-- title:
--   Dwork Power Series Weights: constant Coeff quad Ser
-- statement:
--   The Dwork Power Series Weights construction uses the constant Coeff quad Ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L82-L84

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

theorem Formalism.DworkPowerSeriesWeights.constantCoeff_quadSer (c : ι → ι → K) :
    MvPowerSeries.constantCoeff (quadSer c) = 0 := by sorry
