-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Final_zero_free_region_gl2_prime_choice_results
-- name    : Formalism.HermitianLattices.Final.zero_free_region_gl2_prime_choice_results
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:35.7622+00:00
-- url     : https://prove2.me/theorems/3bbec8f3-c2bc-4853-874e-c3f78b0369a3
-- title:
--   Final: zero free region gl2 prime choice results
-- statement:
--   The Final construction uses the zero free region gl2 prime choice results property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/ZeroFreeRegionGl2PrimeChoiceResults.lean#L10-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/ZeroFreeRegionGl2PrimeChoiceResults.lean#L10-L86

import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NumericalZeroDensityBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterEstimateOfHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NormOneEstimateOfHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TwistIsPrimitiveCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Definitions.Def_Formalism_GL3MeanSquares_ZeroFreeRegionGl2PrimeChoiceResults
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Final

theorem Formalism.HermitianLattices.Final.zero_free_region_gl2_prime_choice_results :
    Formalism.HermitianLattices.ZeroFreeRegionGL2.WGIdentity ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.WGLipschitz ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.WeightedSumLipschitzTrivial ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSumLipschitzOfChebyshev ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.GFiniteSplit ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.MarkovDiscard ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.UnitModulusIncrementConditions ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimorialBound ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ClassAdmissible ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ClassSplit ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.IncrementSizeConditions ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TwEval ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TwPrimitive ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimePairOfBoxAndMeanSquareHypotheses ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.LogNE ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ExpSplit ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.SmoothingSizeBounds ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ThinIntegral ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.CharacterSmoothingEstimate ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.NoExcOfBox ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.RealCharCount ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.NormOneCongr ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.NormOneCongrGeneral ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ExponentialRangeSizeConditions ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimeEstimateOfIntervalHyp ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ExclusionInequalities ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ChoiceOfTwoPrimes ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ReciprocalWeightSizeConditions ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.SecondEstimateOfIntervalHypothesis ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TstarSize ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.ChoiceOfExponentConstant ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimeBoundOfUptoHyp ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.LogPrimeSizeBound ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.IsNormOneIff ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TypeSign ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.TypeSignOfSplit ∧
    Formalism.HermitianLattices.ZeroFreeRegionGL2.SplitsIffJacobi := by sorry
