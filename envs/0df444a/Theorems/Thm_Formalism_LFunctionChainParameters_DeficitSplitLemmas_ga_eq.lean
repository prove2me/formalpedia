-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_ga_eq
-- name    : Formalism.LFunctionChainParameters.DeficitSplitLemmas.ga_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:09.142408+00:00
-- url     : https://prove2.me/theorems/3b9cb682-bc1a-46be-b6f7-dfdfdfb1877a
-- title:
--   Deficit Split Lemmas: ga eq
-- statement:
--   The Deficit Split Lemmas construction uses the ga eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L13-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean#L13-L51

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

theorem Formalism.LFunctionChainParameters.DeficitSplitLemmas.ga_eq {ι κ : Type*} (W : Finset ι) (below : ι → ℕ) (l : ι → ℝ) (Ps : Finset ℕ)
    (J : Finset κ) (gainW : κ → ι → ℝ) (tauW : ι → ℝ) (gain : κ → ℕ → ℝ) (tau : ℕ → ℝ)
    (h : UnitRule W below l Ps J gainW tauW gain tau) :
    GaW W J l gainW tauW = ∑ p ∈ Ps, 2 * Real.log p * ((∑ j ∈ J, gain j p) - tau p) := by sorry
