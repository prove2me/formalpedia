-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_mul_chC_eq_zero_iff
-- name    : Formalism.LFunctionChainParameters.characterSumData.PB.mul_chC_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:11.784058+00:00
-- url     : https://prove2.me/theorems/bace62f4-8800-4286-b47d-4f6e0dd7feda
-- title:
--   PB: mul ch C eq zero iff
-- statement:
--   The PB construction uses the mul ch C eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L109-L119

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_D5_Bal_mul_chC_eq_zero_iff

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

theorem Formalism.LFunctionChainParameters.characterSumData.PB.mul_chC_eq_zero_iff (ψ : AddChar (E0 × H) ℂ) : ψ * chC = 0 ↔ ψ = chC := by sorry
