-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_dirD_X
-- name    : Formalism.DworkPowerSeriesWeights.dirD_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:45.219326+00:00
-- url     : https://prove2.me/theorems/e8157b83-2bb1-4d87-88de-dfdf129e6dab
-- title:
--   Dwork Power Series Weights: dir D X
-- statement:
--   The Dwork Power Series Weights construction uses the dir D X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffQuadSer.lean#L42-L49

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

theorem Formalism.DworkPowerSeriesWeights.dirD_X (L : ι → K) (x : ι) : dirD L (MvPowerSeries.X x) = MvPowerSeries.C (L x) := by sorry
