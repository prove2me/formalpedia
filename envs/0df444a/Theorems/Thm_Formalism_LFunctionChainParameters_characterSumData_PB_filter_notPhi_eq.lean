-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_filter_notPhi_eq
-- name    : Formalism.LFunctionChainParameters.characterSumData.PB.filter_notPhi_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:49.328952+00:00
-- url     : https://prove2.me/theorems/8514d8ca-5748-4137-b889-1445e4a34819
-- title:
--   PB: filter not Phi eq
-- statement:
--   The PB construction uses the filter not Phi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L36-L39

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

theorem Formalism.LFunctionChainParameters.characterSumData.PB.filter_notPhi_eq (t : H) :
    (univ.filter (fun g : E0 × H => ¬ InPhi g)) = univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)) := by sorry
