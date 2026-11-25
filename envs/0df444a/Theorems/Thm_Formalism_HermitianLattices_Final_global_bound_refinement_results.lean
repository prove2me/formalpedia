-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Final_global_bound_refinement_results
-- name    : Formalism.HermitianLattices.Final.global_bound_refinement_results
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:54.140269+00:00
-- url     : https://prove2.me/theorems/f51832c7-2ffc-4e97-8361-00b9facc1ce1
-- title:
--   Final: global bound refinement results
-- statement:
--   The Final construction uses the global bound refinement results property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GlobalBoundRefinementResults.lean#L5-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GlobalBoundRefinementResults.lean#L5-L41

import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_Formalism_GL3MeanSquares_GlobalBoundRefinementResults
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Final

theorem Formalism.HermitianLattices.Final.global_bound_refinement_results :
    Formalism.HermitianLattices.GlobalBoundRefinements.ShortIntervalLowerBound ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.PrimeDivisorCountAbsorption ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.ShortIntervalImpliesProgressions ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.LipschitzWeightedSums ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.ParallelogramMax ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.BRValuation ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.Ms_min ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.LogLFunctionEulerBound ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.RankThresholdInequalityEventually ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.RankMulPowThreeHalvesLeFourthPower ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.DimensionMassJointBound ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.DiscriminantTermBound ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.TableauExponentRange ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.IndicatorKernelSum ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.CharactersCancelScalar ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.TriangularSumExponentBound ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.ExponentBudgetLogBound ∧
    Formalism.HermitianLattices.GlobalBoundRefinements.InvNormSqConjRatioPowIdentities := by sorry
