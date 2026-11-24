-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_local_d
-- name    : Formalism.LFunctionChainParameters.characterSumData.local_d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:10.691337+00:00
-- url     : https://prove2.me/theorems/95f93fbc-bfb6-4a34-8058-d1d669f0c6f3
-- title:
--   character Sum Data: local d
-- statement:
--   The character Sum Data construction uses the local d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L496-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L496-L516

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

theorem Formalism.LFunctionChainParameters.characterSumData.local_d (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    ∑ i ∈ Icc 1 N, (Real.log D.d : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        Kc D (D.d ^ i) g * Fc a t w (D.d ^ i) g
      = ((Real.log D.d * askD D N a t w : ℝ) : ℂ) := by sorry
