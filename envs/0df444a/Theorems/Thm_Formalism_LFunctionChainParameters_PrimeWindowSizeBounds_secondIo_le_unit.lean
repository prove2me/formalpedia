-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_secondIo_le_unit
-- name    : Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.secondIo_le_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:44.362604+00:00
-- url     : https://prove2.me/theorems/92618c13-a46c-4420-b4e3-fd917a4a830c
-- title:
--   Prime Window Size Bounds: second Io le unit
-- statement:
--   The Prime Window Size Bounds construction uses the second Io le unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L811-L816
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/OneLeThresholdMulPowers.lean#L811-L816

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

theorem Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.secondIo_le_unit {P : Par} {e K m T : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K)
    (hm : 0 ≤ m) (hT : 1 ≤ T) : tSecondIo P m T ≤ unitU P m T := by sorry
