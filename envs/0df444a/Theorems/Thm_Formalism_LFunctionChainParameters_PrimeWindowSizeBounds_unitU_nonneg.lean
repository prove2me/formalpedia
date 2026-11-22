-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_unitU_nonneg
-- name    : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.unitU_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:08.140966+00:00
-- url     : https://prove2.me/theorems/5ff7a772-a9d2-4781-a395-3929f8bfebac
-- title:
--   Prime Window Size Bounds: unit U nonneg
-- statement:
--   The Prime Window Size Bounds construction uses the unit U nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L795-L799
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L795-L799

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

theorem Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.unitU_nonneg {P : Par} {m T : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) : 0 ≤ unitU P m T := by sorry
