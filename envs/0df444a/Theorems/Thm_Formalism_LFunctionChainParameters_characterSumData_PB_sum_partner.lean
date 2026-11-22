-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_sum_partner
-- name    : Formalism.LFunctionChainParameters.characterSumData.PB.sum_partner
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:12.050849+00:00
-- url     : https://prove2.me/theorems/58b655e6-1c4e-4c30-99be-d94ab886d9c0
-- title:
--   PB: sum partner
-- statement:
--   The PB construction uses the sum partner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L47-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L47-L67

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

theorem Formalism.LFunctionChainParameters.characterSumData.PB.sum_partner {β : Type*} [AddCommMonoid β] (t : H) (F : E0 × H → β) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), F (partner t g) = ∑ ρ ∈ PhiSet (H := H), F ρ := by sorry
