-- Prove2me | Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_max_zero_of_gt
-- name    : Formalism.LFunctionChainParameters.characterSumData.max_zero_of_gt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:24.795897+00:00
-- url     : https://prove2.me/theorems/afa53b78-bd7e-466b-ae11-44bcf7006f4c
-- title:
--   character Sum Data: max zero of gt
-- statement:
--   The character Sum Data construction uses the max zero of gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L399-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/StronglyIrreducible.lean#L399-L410

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

theorem Formalism.LFunctionChainParameters.characterSumData.max_zero_of_gt {N : ℕ} {a : ℝ} {t : H} {w : E0 × H → ℝ} (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) {g : E0 × H} (hg : ¬ InPhi g) {m : ℝ} (hm : (N : ℝ) < m) :
    max (a / m - w (partner t g)) 0 = 0 := by sorry
