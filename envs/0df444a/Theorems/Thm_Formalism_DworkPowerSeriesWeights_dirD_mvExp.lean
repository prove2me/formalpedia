-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_mvExp
-- name    : Formalism.DworkPowerSeriesWeights.dirD_mvExp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:39.461816+00:00
-- url     : https://prove2.me/theorems/e8aee9c7-d87d-421d-972d-4b5fcfa9ace0
-- title:
--   Dwork Power Series Weights: dir D mv Exp
-- statement:
--   The Dwork Power Series Weights construction uses the dir D mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L117-L123

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

theorem Formalism.DworkPowerSeriesWeights.dirD_mvExp (L : ι → K) (f : MvPowerSeries ι K) (hf : MvPowerSeries.constantCoeff f = 0) :
    dirD L (mvExp f) = dirD L f * mvExp f := by sorry
