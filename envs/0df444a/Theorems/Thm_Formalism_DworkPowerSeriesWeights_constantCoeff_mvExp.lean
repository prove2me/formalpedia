-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_mvExp
-- name    : Formalism.DworkPowerSeriesWeights.constantCoeff_mvExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:43.568527+00:00
-- url     : https://prove2.me/theorems/939f90b9-c961-4c22-bae5-83afa1a7006d
-- title:
--   Dwork Power Series Weights: constant Coeff mv Exp
-- statement:
--   The Dwork Power Series Weights construction uses the constant Coeff mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L125-L132

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
variable {K : Type u} [NormedField K] [CharZero K] {ι : Type} [Fintype ι]

theorem Formalism.DworkPowerSeriesWeights.constantCoeff_mvExp (f : MvPowerSeries ι K) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (mvExp f) = 1 := by sorry
