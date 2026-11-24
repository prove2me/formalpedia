-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceDualSums_sum_zmod
-- name    : Formalism.L2.Th1.D.TraceDualSums.sum_zmod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:45:00.085871+00:00
-- url     : https://prove2.me/theorems/47c5e6ca-15ae-4779-8be1-f88090c1662d
-- title:
--   Trace Dual Sums: sum zmod
-- statement:
--   The Trace Dual Sums construction uses the sum zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TraceDualExists.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TraceDualExists.lean#L13-L19

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

theorem Formalism.L2.Th1.D.TraceDualSums.sum_zmod {M : Type} [AddCommMonoid M] (d : ℕ) [NeZero d] (F : ℕ → M) :
    (∑ s : ZMod d, F s.val) = ∑ i ∈ Finset.range d, F i := by sorry
