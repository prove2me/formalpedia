-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceDualSums_sum_range_even
-- name    : Formalism.L2.Th1.D.TraceDualSums.sum_range_even
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:45:19.871446+00:00
-- url     : https://prove2.me/theorems/58120550-4420-4abc-96ec-2c4bc17f56f8
-- title:
--   Trace Dual Sums: sum range even
-- statement:
--   The Trace Dual Sums construction uses the sum range even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TraceDualExists.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TraceDualExists.lean#L21-L31

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.D.TraceDualSums

theorem Formalism.L2.Th1.D.TraceDualSums.sum_range_even {M : Type} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    (∑ i ∈ Finset.range (2 * m), if i % 2 = 0 then g i else 0) =
      ∑ k ∈ Finset.range m, g (2 * k) := by sorry
