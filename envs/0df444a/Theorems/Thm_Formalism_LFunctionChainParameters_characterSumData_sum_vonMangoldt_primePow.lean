-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_sum_vonMangoldt_primePow
-- name    : Formalism.LFunctionChainParameters.characterSumData.sum_vonMangoldt_primePow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:19.121289+00:00
-- url     : https://prove2.me/theorems/4cd2eb9e-f836-48ad-9ceb-ace476354a52
-- title:
--   character Sum Data: sum von Mangoldt prime Pow
-- statement:
--   The character Sum Data construction uses the sum von Mangoldt prime Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L335-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L335-L393

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

theorem Formalism.LFunctionChainParameters.characterSumData.sum_vonMangoldt_primePow (N : ℕ) (X : ℕ → ℂ)
    (hX : ∀ p i, p.Prime → 1 ≤ i → N < p ^ i → X (p ^ i) = 0) :
    ∑ n ∈ Icc 1 N, (Λ n : ℂ) * X n
      = ∑ p ∈ (range (N + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * X (p ^ i) := by sorry
