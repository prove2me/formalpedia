-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_term_real
-- name    : Formalism.LFunctionChainParameters.characterSumData.term_real
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:47.638942+00:00
-- url     : https://prove2.me/theorems/325fb6d2-fd92-49e9-9e96-1aa108d1a993
-- title:
--   character Sum Data: term real
-- statement:
--   The character Sum Data construction uses the term real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L612-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L612-L617

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_D5_Bal_term_real

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

theorem Formalism.LFunctionChainParameters.characterSumData.term_real (a w : ℝ) (hw : w ≠ 0) (n : ℕ) : a / n - w = w * (a / w / n - 1) := by sorry
