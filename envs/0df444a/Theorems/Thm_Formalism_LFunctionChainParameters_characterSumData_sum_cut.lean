-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_sum_cut
-- name    : Formalism.LFunctionChainParameters.characterSumData.sum_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:25.924488+00:00
-- url     : https://prove2.me/theorems/36a1f013-993f-41b3-8ab0-f7a544497fda
-- title:
--   character Sum Data: sum cut
-- statement:
--   The character Sum Data construction uses the sum cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L619-L653
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L619-L653

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

theorem Formalism.LFunctionChainParameters.characterSumData.sum_cut (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (N : ℕ) (a W : ℝ) (ha : 0 < a) (hW : 0 < W)
    (hN : a / W ≤ N) :
    ∑ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - W) 0 : ℝ) : ℂ)
      = ∑ n ∈ Icc 1 ⌊a / W⌋₊, (Λ n : ℂ) * primVal D ψ n * ((a / n - W : ℝ) : ℂ) := by sorry
