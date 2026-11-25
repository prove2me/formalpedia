-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Final_trace_integrality_results
-- name    : Formalism.HermitianLattices.Final.trace_integrality_results
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:20.396011+00:00
-- url     : https://prove2.me/theorems/61e4a7dc-5852-49b3-ac9c-031532c25c5d
-- title:
--   Final: trace integrality results
-- statement:
--   The Final construction uses the trace integrality results property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/TraceIntegralityResults.lean#L12-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/TraceIntegralityResults.lean#L12-L74

import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentFromBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MinkowskiDivisorBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SeparatedSetPackingBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BlockOperatorNormBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HookRowProductEqFactorial
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OrthogonalMinorBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumLogFactorialRowsBounds
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentArithmeticBound
import Definitions.Def_Formalism_GL3MeanSquares_TraceIntegralityResults
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Final

theorem Formalism.HermitianLattices.Final.trace_integrality_results :
    Formalism.HermitianLattices.TraceIntegrality.Ms_arith ∧
    Formalism.HermitianLattices.TraceIntegrality.Ms_index ∧
    Formalism.HermitianLattices.TraceIntegrality.Minkowski_div ∧
    Formalism.HermitianLattices.TraceIntegrality.Minkowski_log ∧
    Formalism.HermitianLattices.TraceIntegrality.Weight_change ∧
    Formalism.HermitianLattices.TraceIntegrality.SeparatedSetPackingBound ∧
    Formalism.HermitianLattices.TraceIntegrality.PackingCountBound ∧
    Formalism.HermitianLattices.TraceIntegrality.LayerCakeSumBound ∧
    Formalism.HermitianLattices.TraceIntegrality.FockMonomialOrthogonality ∧
    Formalism.HermitianLattices.TraceIntegrality.JetsProductBound ∧
    Formalism.HermitianLattices.TraceIntegrality.BlockOperatorNormBound ∧
    Formalism.HermitianLattices.TraceIntegrality.ZetaValueArithmetic ∧
    Formalism.HermitianLattices.TraceIntegrality.HookLengthFormula ∧
    Formalism.HermitianLattices.TraceIntegrality.LargestPlaceHookBound ∧
    Formalism.HermitianLattices.TraceIntegrality.ThinPlaceHookBound ∧
    Formalism.HermitianLattices.TraceIntegrality.Sqm_from ∧
    Formalism.HermitianLattices.TraceIntegrality.MeanLogNormBound ∧
    Formalism.HermitianLattices.TraceIntegrality.DegreeEqHeadMinusBalance ∧
    Formalism.HermitianLattices.TraceIntegrality.WeylDimensionBounds ∧
    Formalism.HermitianLattices.TraceIntegrality.CoordinatesBoundedByBalance ∧
    Formalism.HermitianLattices.TraceIntegrality.InjectiveReindexNormLe ∧
    Formalism.HermitianLattices.TraceIntegrality.ZetaBoundApplication ∧
    Formalism.HermitianLattices.TraceIntegrality.OrthogonalMinorBound ∧
    Formalism.HermitianLattices.TraceIntegrality.AmGmSumLowerBound ∧
    Formalism.HermitianLattices.TraceIntegrality.LastMinimumSqBoundOfProductBound ∧
    Formalism.HermitianLattices.TraceIntegrality.ConcavityEquidistribution ∧
    Formalism.HermitianLattices.TraceIntegrality.LastColumnBound ∧
    Formalism.HermitianLattices.TraceIntegrality.PropZ_i ∧
    Formalism.HermitianLattices.TraceIntegrality.PropZ_ii ∧
    Formalism.HermitianLattices.TraceIntegrality.PropZ_iii ∧
    Formalism.HermitianLattices.TraceIntegrality.PropZ_tail := by sorry
