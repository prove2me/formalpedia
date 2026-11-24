-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_local_unram
-- name    : Formalism.LFunctionChainParameters.characterSumData.local_unram
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:49:43.404782+00:00
-- url     : https://prove2.me/theorems/6dfaef58-8224-4703-a50c-d1da71d57158
-- title:
--   character Sum Data: local unram
-- statement:
--   The character Sum Data construction uses the local unram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L452-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L452-L473

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

theorem Formalism.LFunctionChainParameters.characterSumData.local_unram (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hq : p ≠ D.q1) (hd : p ≠ D.d) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) := by sorry
