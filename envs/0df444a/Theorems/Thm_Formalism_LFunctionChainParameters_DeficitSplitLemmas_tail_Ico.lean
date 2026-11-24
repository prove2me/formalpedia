-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_tail_Ico
-- name    : Formalism.LFunctionChainParameters.DeficitSplitLemmas.tail_Ico
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:49:16.693736+00:00
-- url     : https://prove2.me/theorems/f2ea57e4-f49a-4324-8af0-9931c292e1ad
-- title:
--   Deficit Split Lemmas: tail Ico
-- statement:
--   The Deficit Split Lemmas construction uses the tail Ico property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L204-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L204-L218

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

theorem Formalism.LFunctionChainParameters.DeficitSplitLemmas.tail_Ico (p₀ : ℕ) (hp : 3 ≤ p₀) (K : ℕ) :
    ∑ n ∈ Finset.Ico p₀ (p₀ + K), Real.log n / (n : ℝ) ^ 2 ≤
      2 * (gT ((p₀ : ℝ) - 1) - gT ((p₀ : ℝ) + K - 1)) := by sorry
