-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_inner_eq
-- name    : Formalism.LFunctionChainParameters.characterSumData.inner_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:21.256813+00:00
-- url     : https://prove2.me/theorems/df5e3fec-d26e-441a-982d-6b075a73ba69
-- title:
--   character Sum Data: inner eq
-- statement:
--   The character Sum Data construction uses the inner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L655-L688
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L655-L688

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

theorem Formalism.LFunctionChainParameters.characterSumData.inner_eq (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) :
    ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * primVal D ψ n * ((a / n - w : ℝ) : ℂ)
      = (w : ℂ) * GPsi D ell ψ (a / w) + (if ψ = 0 then
          ((a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * ell ψ) := by sorry
