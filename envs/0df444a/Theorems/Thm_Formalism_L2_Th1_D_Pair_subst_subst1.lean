-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_subst1
-- name    : Formalism.L2.Th1.D.Pair.subst_subst1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:39.717411+00:00
-- url     : https://prove2.me/theorems/323fce32-aa7f-48e3-bd0c-d53b12dc0dd1
-- title:
--   Pair: subst subst1
-- statement:
--   The Pair construction uses the subst subst1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstFirstCoboundaryThree.lean#L34-L40

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

theorem Formalism.L2.Th1.D.Pair.subst_subst1 {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    {a : MvPowerSeries ι K} (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by sorry
