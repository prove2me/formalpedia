-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_tail_step
-- name    : Formalism.LFunctionChainParameters.DeficitSplitLemmas.tail_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:32.006799+00:00
-- url     : https://prove2.me/theorems/8acae489-b0c4-4d37-bb70-af242d95e0fa
-- title:
--   Deficit Split Lemmas: tail step
-- statement:
--   The Deficit Split Lemmas construction uses the tail step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L168-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L168-L197

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section

theorem Formalism.LFunctionChainParameters.DeficitSplitLemmas.tail_step (y : ℝ) (hy : 3 ≤ y) : Real.log y / y ^ 2 ≤ 2 * (gT (y - 1) - gT y) := by sorry
