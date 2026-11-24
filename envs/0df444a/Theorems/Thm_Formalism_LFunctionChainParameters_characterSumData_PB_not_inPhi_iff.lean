-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_not_inPhi_iff
-- name    : Formalism.LFunctionChainParameters.characterSumData.PB.not_inPhi_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:52.182038+00:00
-- url     : https://prove2.me/theorems/90d16963-2c1c-4bd9-81b8-80f04754b7a0
-- title:
--   PB: not in Phi iff
-- statement:
--   The PB construction uses the not in Phi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L23-L25

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

theorem Formalism.LFunctionChainParameters.characterSumData.PB.not_inPhi_iff (g : E0 × H) : ¬ InPhi g ↔ g.1.1 = 1 := by sorry
