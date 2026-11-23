-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_Model_sizes
-- name    : Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model.sizes
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:19.166271+00:00
-- url     : https://prove2.me/theorems/5096cffb-e5bd-4fa1-824c-31c6231f27f4
-- title:
--   Model: sizes
-- statement:
--   The Model construction uses the sizes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SlopeInequalityOfLattices.lean#L407-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SlopeInequalityOfLattices.lean#L407-L414

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model

theorem Formalism.LFunctionChainParameters.LatticeToWeightTransfer.Model.sizes (μ0 μ1 μ2 : ℝ) (h : Fin 20 → ℝ) :
    SizesPrim (D1 μ0 μ1 μ2 h) C2 |RdV| 1 (fun _ _ => Q0 μ0 μ1) := by sorry
