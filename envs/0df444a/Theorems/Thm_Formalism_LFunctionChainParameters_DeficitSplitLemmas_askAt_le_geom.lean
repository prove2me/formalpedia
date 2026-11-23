-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_askAt_le_geom
-- name    : Formalism.LFunctionChainParameters.DeficitSplitLemmas.askAt_le_geom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:07.735047+00:00
-- url     : https://prove2.me/theorems/dfa5fd40-fbf8-4c17-8d8b-efff2b0d9677
-- title:
--   Deficit Split Lemmas: ask At le geom
-- statement:
--   The Deficit Split Lemmas construction uses the ask At le geom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L242-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L242-L252

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

theorem Formalism.LFunctionChainParameters.DeficitSplitLemmas.askAt_le_geom (I : Finset ℕ) (at_ p : ℝ) (w : ℕ → ℝ) (hp : 0 < p) (ha : 0 ≤ at_)
    (hw : ∀ i ∈ I, 0 ≤ w i) : askAt I at_ p w ≤ at_ * ∑ i ∈ I, (1 / p) ^ i := by sorry
