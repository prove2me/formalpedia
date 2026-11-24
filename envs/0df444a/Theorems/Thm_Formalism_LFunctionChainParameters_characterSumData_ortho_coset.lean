-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_ortho_coset
-- name    : Formalism.LFunctionChainParameters.characterSumData.ortho_coset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:03.611041+00:00
-- url     : https://prove2.me/theorems/31c02139-13db-4378-9d9e-1738997738e3
-- title:
--   character Sum Data: ortho coset
-- statement:
--   The character Sum Data construction uses the ortho coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L274-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L274-L304

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
open Classical

theorem Formalism.LFunctionChainParameters.characterSumData.ortho_coset (I : AddSubgroup (E0 × H)) (h g : E0 × H) :
    (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * cosetMean I h ψ
      = if g - h ∈ I then 2 / (Nat.card I : ℂ) else 0 := by sorry
