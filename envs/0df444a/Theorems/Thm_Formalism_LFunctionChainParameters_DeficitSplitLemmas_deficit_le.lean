-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_deficit_le
-- name    : Formalism.LFunctionChainParameters.DeficitSplitLemmas.deficit_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:26.560013+00:00
-- url     : https://prove2.me/theorems/484b7821-8e7e-4533-aca8-15cf38df2c84
-- title:
--   Deficit Split Lemmas: deficit le
-- statement:
--   The Deficit Split Lemmas construction uses the deficit le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L70-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L70-L85

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

theorem Formalism.LFunctionChainParameters.DeficitSplitLemmas.deficit_le {κ τ : Type*} (J : Finset κ) (TT : Finset τ) (TTp : ℕ → Finset τ)
    (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (gain : κ → ℕ → ℝ) (tau lo fl : ℕ → ℝ) (p : ℕ)
    (h : SizeData₂ J TT TTp vonMangoldtClassSum gain tau lo fl p) :
    deficit J TT vonMangoldtClassSum gain tau p ≤ servedLoss J TT TTp vonMangoldtClassSum lo fl p := by sorry
