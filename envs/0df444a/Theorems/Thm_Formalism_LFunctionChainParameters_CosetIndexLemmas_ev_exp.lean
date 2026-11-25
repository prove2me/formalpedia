-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_CosetIndexLemmas_ev_exp
-- name    : Formalism.LFunctionChainParameters.CosetIndexLemmas.ev_exp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:34:07.881705+00:00
-- url     : https://prove2.me/theorems/5227bea8-716a-4ae7-a5bf-8f976925ec64
-- title:
--   Coset Index Lemmas: ev exp
-- statement:
--   The Coset Index Lemmas construction uses the ev exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DisplayedInequalitySharpHalf.lean#L91-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/DisplayedInequalitySharpHalf.lean#L91-L121

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.CosetIndexLemmas
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost
open Filter Asymptotics

theorem Formalism.LFunctionChainParameters.CosetIndexLemmas.ev_exp (A B κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x, x₀ ≤ x → A * x ^ B ≤ Real.exp (κ * x ^ δ) := by sorry
