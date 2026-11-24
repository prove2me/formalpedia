-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_partner_inPhi
-- name    : Formalism.LFunctionChainParameters.characterSumData.partner_inPhi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:12.335801+00:00
-- url     : https://prove2.me/theorems/e2217379-c5f1-456c-bbb8-b16fa9c5d085
-- title:
--   character Sum Data: partner in Phi
-- statement:
--   The character Sum Data construction uses the partner in Phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L395-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L395-L397

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
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem Formalism.LFunctionChainParameters.characterSumData.partner_inPhi {g : E0 × H} (t : H) (hg : ¬ InPhi g) : InPhi (partner t g) := by sorry
