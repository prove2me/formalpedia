-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_C
-- name    : Formalism.DworkPowerSeriesWeights.dirD_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:10.704448+00:00
-- url     : https://prove2.me/theorems/2adb8084-ddf2-4a8d-b2ed-686db32449ec
-- title:
--   Dwork Power Series Weights: dir D C
-- statement:
--   The Dwork Power Series Weights construction uses the dir D C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L51-L53

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

theorem Formalism.DworkPowerSeriesWeights.dirD_C (L : ι → K) (a : K) : dirD L (MvPowerSeries.C a : MvPowerSeries ι K) = 0 := by sorry
