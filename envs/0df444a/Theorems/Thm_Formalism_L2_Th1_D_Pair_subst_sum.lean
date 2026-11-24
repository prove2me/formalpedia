-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum
-- name    : Formalism.L2.Th1.D.Pair.subst_sum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:17.729797+00:00
-- url     : https://prove2.me/theorems/a4c981dd-f2d3-48f5-97fc-908c5bba0412
-- title:
--   Pair: subst sum
-- statement:
--   The Pair construction uses the subst sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L208-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L208-L213

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.D.Pair.subst_sum {ι κ α : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ) (s : Finset α)
    (f : α → MvPowerSeries ι K) : subst φ (∑ r ∈ s, f r) = ∑ r ∈ s, subst φ (f r) := by sorry
