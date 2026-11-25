-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_joint_size_bound_alt
-- name    : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.joint_size_bound_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:02.535842+00:00
-- url     : https://prove2.me/theorems/f8f2bf8a-b7b0-4f49-9eb8-399de62ff3bf
-- title:
--   Prime Window Size Bounds: joint size bound alt
-- statement:
--   The Prime Window Size Bounds construction uses the joint size bound alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L1102-L1144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L1102-L1144

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr

theorem Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.joint_size_bound_alt : WindowLossesBound := by sorry
