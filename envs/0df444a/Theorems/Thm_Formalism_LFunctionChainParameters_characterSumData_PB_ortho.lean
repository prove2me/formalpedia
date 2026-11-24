-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_ortho
-- name    : Formalism.LFunctionChainParameters.characterSumData.PB.ortho
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:03.473327+00:00
-- url     : https://prove2.me/theorems/7dd6d3c2-fce6-4f53-9a96-230c4b147b26
-- title:
--   PB: ortho
-- statement:
--   The PB construction uses the ortho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L78-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L78-L83

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.LFunctionChainParameters.characterSumData.PB.ortho (g h : E0 × H) :
    ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ψ h
      = if h = g then (Fintype.card (E0 × H) : ℂ) else 0 := by sorry
