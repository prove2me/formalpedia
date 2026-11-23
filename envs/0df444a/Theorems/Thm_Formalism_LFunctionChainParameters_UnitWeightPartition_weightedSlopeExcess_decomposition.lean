-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_UnitWeightPartition_weightedSlopeExcess_decomposition
-- name    : Formalism.LFunctionChainParameters.UnitWeightPartition.weightedSlopeExcess_decomposition
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:11.181248+00:00
-- url     : https://prove2.me/theorems/94f69016-6178-43cd-96ca-05d0be27a99d
-- title:
--   Unit Weight Partition: weighted Slope Excess decomposition
-- statement:
--   The Unit Weight Partition construction uses the weighted Slope Excess decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedSlopeExcessDecomposition.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedSlopeExcessDecomposition.lean#L9-L18

import Definitions.Def_Formalism_SizeWindowBrackets_ClaimGaFree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.UnitWeightPartition
open Finset
variable {ι κ : Type*} [DecidableEq ι]

theorem Formalism.LFunctionChainParameters.UnitWeightPartition.weightedSlopeExcess_decomposition (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau : ι → ℝ) : ClaimSg W J l gain F E tau := by sorry
