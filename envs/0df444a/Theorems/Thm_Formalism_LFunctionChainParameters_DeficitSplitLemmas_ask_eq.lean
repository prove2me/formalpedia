-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_ask_eq
-- name    : Formalism.LFunctionChainParameters.DeficitSplitLemmas.ask_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:35.667707+00:00
-- url     : https://prove2.me/theorems/9290f888-0e89-4f95-847b-a30b5fb98173
-- title:
--   Deficit Split Lemmas: ask eq
-- statement:
--   The Deficit Split Lemmas construction uses the ask eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L53-L61

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

theorem Formalism.LFunctionChainParameters.DeficitSplitLemmas.ask_eq {κ τ : Type*} (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (dT : κ → τ → ℝ) :
    ASK Ps J TT vonMangoldtClassSum dT = (∑ p ∈ Ps, 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT, vonMangoldtClassSum j t p) +
      ∑ j ∈ J, ∑ t ∈ TT, dT j t := by sorry
