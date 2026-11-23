-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_left_zero
-- name    : Formalism.L2.Th1.D.TorusDerivation.subst_left_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:08.69195+00:00
-- url     : https://prove2.me/theorems/60699ad1-79b1-4d45-95af-46bd9df6bab9
-- title:
--   Torus Derivation: subst left zero
-- statement:
--   The Torus Derivation construction uses the subst left zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean#L72-L81

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
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
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.D.TorusDerivation.subst_left_zero {τ : Type} {G : MvPowerSeries (Fin 2) K} (hG : DivAB G)
    {B : MvPowerSeries τ K} (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.subst ![0, B] G = 0 := by sorry
