-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_apply
-- name    : Formalism.DworkPowerSeriesWeights.dirD_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:36.582012+00:00
-- url     : https://prove2.me/theorems/db42b3f6-a97b-49a4-a656-98eb08e4e5df
-- title:
--   Dwork Power Series Weights: dir D apply
-- statement:
--   The Dwork Power Series Weights construction uses the dir D apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L19-L27

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

theorem Formalism.DworkPowerSeriesWeights.dirD_apply (L : ι → K) (F : MvPowerSeries ι K) :
    dirD L F = ∑ x, MvPowerSeries.C (L x) * MvPowerSeries.pderiv K x F := by sorry
