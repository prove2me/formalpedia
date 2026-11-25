-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Final_genus_mass_volume_results
-- name    : Formalism.HermitianLattices.Final.genus_mass_volume_results
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:13.618956+00:00
-- url     : https://prove2.me/theorems/cac2d194-b969-5835-8382-24e743ef25e2
-- title:
--   Final: genus mass volume results
-- statement:
--   The Final construction uses the genus mass volume results property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMassVolumeResults.lean#L14-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMassVolumeResults.lean#L14-L102

import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FiniteEulerProductLeZeta
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OneAddInvPowLeExpOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FactorialProductRearrangement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CardUnitsZmodPrimeSq
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GaussianIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightShiftProduct
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HolderExponentialMoments
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierTransformScaledInner
import Definitions.Def_Formalism_GL3MeanSquares_GenusMassVolumeResults
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Final

theorem Formalism.HermitianLattices.Final.genus_mass_volume_results :
    Formalism.HermitianLattices.GenusMassVolumes.SW_hecke_gap ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_hecke_gap_sharp ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_hecke_terms ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_height_integral ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_real_gaussian ∧
    Formalism.HermitianLattices.GenusMassVolumes.SW_real_decay ∧
    Formalism.HermitianLattices.GenusMassVolumes.ball_volume ∧
    Formalism.HermitianLattices.GenusMassVolumes.SelfDualMeasure ∧
    Formalism.HermitianLattices.GenusMassVolumes.SphereVolumeDerivative ∧
    Formalism.HermitianLattices.GenusMassVolumes.SplitDensity ∧
    Formalism.HermitianLattices.GenusMassVolumes.InertDensity ∧
    Formalism.HermitianLattices.GenusMassVolumes.GlobalArithmeticIdentity ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogLValueFinitePlaces ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogLFunctionEulerBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.WeightedSumEqQuadraticForm ∧
    Formalism.HermitianLattices.GenusMassVolumes.RankLeTwiceMin ∧
    Formalism.HermitianLattices.GenusMassVolumes.OppositeSignRhoDifferenceEqCard ∧
    Formalism.HermitianLattices.GenusMassVolumes.CumulantLowerBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogMomentConvexity ∧
    Formalism.HermitianLattices.GenusMassVolumes.ComplexGaussianIntegral ∧
    Formalism.HermitianLattices.GenusMassVolumes.GaussianRayIntegral ∧
    Formalism.HermitianLattices.GenusMassVolumes.ExponentialTailIntegral ∧
    Formalism.HermitianLattices.GenusMassVolumes.TailNegligible ∧
    Formalism.HermitianLattices.GenusMassVolumes.ThresholdConstantRescaledEpsilonBounds ∧
    Formalism.HermitianLattices.GenusMassVolumes.GrassmannianVolume ∧
    Formalism.HermitianLattices.GenusMassVolumes.JointLowerBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.DegreeLeMulPowSignatureBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.LocalColumnIndex ∧
    Formalism.HermitianLattices.GenusMassVolumes.IndexRatioComparison ∧
    Formalism.HermitianLattices.GenusMassVolumes.RankCountExact ∧
    Formalism.HermitianLattices.GenusMassVolumes.LeastNoncompactGap ∧
    Formalism.HermitianLattices.GenusMassVolumes.RankThresholdInequalityEventually ∧
    Formalism.HermitianLattices.GenusMassVolumes.RankMulPowThreeHalvesLeFourthPower ∧
    Formalism.HermitianLattices.GenusMassVolumes.DimensionMassJointBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.VolumeParameterBounds ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogVolumeLeParameter ∧
    Formalism.HermitianLattices.GenusMassVolumes.BracketCoefficients ∧
    Formalism.HermitianLattices.GenusMassVolumes.LogMassFormula ∧
    Formalism.HermitianLattices.GenusMassVolumes.BracketSumBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.InitialSumIdentity ∧
    Formalism.HermitianLattices.GenusMassVolumes.InterlacedProductComparison ∧
    Formalism.HermitianLattices.GenusMassVolumes.PowerProductTwoSidedBounds ∧
    Formalism.HermitianLattices.GenusMassVolumes.MeanSquareRequiresDegreeBound ∧
    Formalism.HermitianLattices.GenusMassVolumes.NormalizedLogRatioVandermondeVariation := by sorry
