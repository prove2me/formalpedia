-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_dsum_le
-- name    : Formalism.LFunctionChainParameters.DeficitSplitLemmas.dsum_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:04.61466+00:00
-- url     : https://prove2.me/theorems/93422edb-66ca-4bd4-8544-6433e00aea29
-- title:
--   Deficit Split Lemmas: dsum le
-- statement:
--   The Deficit Split Lemmas construction uses the dsum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L750-L760
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L750-L760

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

theorem Formalism.LFunctionChainParameters.DeficitSplitLemmas.dsum_le {κ τ : Type*} (J : Finset κ) (S : Finset τ) (g : κ → τ → ℝ) (c : ℝ)
    (h : ∀ j ∈ J, ∀ t ∈ S, g j t ≤ c) :
    ∑ j ∈ J, ∑ t ∈ S, g j t ≤ (J.card : ℝ) * S.card * c := by sorry
