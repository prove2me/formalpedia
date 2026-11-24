-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_LErr_umean_le_of_le
-- name    : Formalism.LFunctionChainParameters.LErr.umean_le_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:39.827568+00:00
-- url     : https://prove2.me/theorems/d71db1e2-9f89-4e4f-944a-af7c202315e1
-- title:
--   LErr: umean le of le
-- statement:
--   The LErr construction uses the umean le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L209-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean#L209-L218

import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SubThreeMulLogTwoLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LErr
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
set_option linter.unusedVariables false

theorem Formalism.LFunctionChainParameters.LErr.umean_le_of_le {ι : Type} [Fintype ι] (X : ι → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i, X i ≤ B) :
    umean X ≤ B := by sorry
