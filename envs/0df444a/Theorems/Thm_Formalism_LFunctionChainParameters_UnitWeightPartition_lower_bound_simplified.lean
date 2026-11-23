-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_UnitWeightPartition_lower_bound_simplified
-- name    : Formalism.LFunctionChainParameters.UnitWeightPartition.lower_bound_simplified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:15.247826+00:00
-- url     : https://prove2.me/theorems/c4aa36b4-625b-41a7-ae23-d8a86c23e2e5
-- title:
--   Unit Weight Partition: lower bound simplified
-- statement:
--   The Unit Weight Partition construction uses the lower bound simplified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedSlopeExcessDecomposition.lean#L180-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/WeightedSlopeExcessDecomposition.lean#L180-L189

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

theorem Formalism.LFunctionChainParameters.UnitWeightPartition.lower_bound_simplified (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ)
    (gain F E : κ → ι → ℝ) (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ)
    (f T b muM IOp LT RX : ℝ) :
    ClaimLow2 W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd f T b muM IOp LT RX := by sorry
