-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_conj_eq_neg
-- name    : Formalism.LFunctionChainParameters.characterSumData.PB.conj_eq_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:13.359799+00:00
-- url     : https://prove2.me/theorems/04e0cbd8-efb6-493c-bc23-4aa1cc6f034f
-- title:
--   PB: conj eq neg
-- statement:
--   The PB construction uses the conj eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L73-L76

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

theorem Formalism.LFunctionChainParameters.characterSumData.PB.conj_eq_neg (ψ : AddChar (E0 × H) ℂ) (g : E0 × H) : starRingEnd ℂ (ψ g) = ψ (-g) := by sorry
