-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_inPhi_nsmul
-- name    : Formalism.LFunctionChainParameters.characterSumData.PB.inPhi_nsmul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:47.316626+00:00
-- url     : https://prove2.me/theorems/80247edc-0514-47ec-8eed-c5d91a80c03b
-- title:
--   PB: in Phi nsmul
-- statement:
--   The PB construction uses the in Phi nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L31-L34

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

theorem Formalism.LFunctionChainParameters.characterSumData.PB.inPhi_nsmul {x : E0 × H} (hx : InPhi x) (i : ℕ) : InPhi (i • x) := by sorry
