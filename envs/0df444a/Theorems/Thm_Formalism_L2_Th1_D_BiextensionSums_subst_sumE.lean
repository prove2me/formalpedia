-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_BiextensionSums_subst_sumE
-- name    : Formalism.L2.Th1.D.BiextensionSums.subst_sumE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:37:54.812145+00:00
-- url     : https://prove2.me/theorems/869dbe5d-f8e5-4cb6-8436-7b3d88c23d69
-- title:
--   Biextension Sums: subst sum E
-- statement:
--   The Biextension Sums construction uses the subst sum E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionPointsOfExpSpec.lean#L30-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/BiextensionPointsOfExpSpec.lean#L30-L42

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionSums

theorem Formalism.L2.Th1.D.BiextensionSums.subst_sumE {K ι κ : Type} [Field K] [Fintype ι] {N0 N1 : ℕ}
    {Xt : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries κ K}
    (h0 : ∀ x, constantCoeff (Xt x) = 0) (be : MvPowerSeries (Fin 2) K) :
    subst Xt (sumE be) = ∑ e : ι × Fin N0 × Fin N1, subst ![Xt (false, e), Xt (true, e)] be := by sorry
