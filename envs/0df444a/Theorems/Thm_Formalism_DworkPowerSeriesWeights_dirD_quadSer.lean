-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_quadSer
-- name    : Formalism.DworkPowerSeriesWeights.dirD_quadSer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:34.916687+00:00
-- url     : https://prove2.me/theorems/4f0e30b8-1d50-4a70-8872-524207098a28
-- title:
--   Dwork Power Series Weights: dir D quad Ser
-- statement:
--   The Dwork Power Series Weights construction uses the dir D quad Ser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L59-L66

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

theorem Formalism.DworkPowerSeriesWeights.dirD_quadSer (c : ι → ι → K) (L : ι → K) : dirD L (quadSer c) = linSer c L := by sorry
