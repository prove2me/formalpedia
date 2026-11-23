-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_deficit_dropped
-- name    : Formalism.LFunctionChainParameters.DeficitSplitLemmas.deficit_dropped
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:11.819647+00:00
-- url     : https://prove2.me/theorems/177be166-1e28-4153-8fff-b692d5161b65
-- title:
--   Deficit Split Lemmas: deficit dropped
-- statement:
--   The Deficit Split Lemmas construction uses the deficit dropped property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L87-L91

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

theorem Formalism.LFunctionChainParameters.DeficitSplitLemmas.deficit_dropped {κ τ : Type*} (J : Finset κ) (TT : Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ)
    (gain : κ → ℕ → ℝ) (tau : ℕ → ℝ) (p : ℕ) (hg : ∀ j ∈ J, gain j p = 0) (ht : tau p = 0) :
    deficit J TT vonMangoldtClassSum gain tau p = wholeAsk J TT vonMangoldtClassSum p := by sorry
