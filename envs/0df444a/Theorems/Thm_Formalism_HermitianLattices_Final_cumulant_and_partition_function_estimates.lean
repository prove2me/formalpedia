-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Final_cumulant_and_partition_function_estimates
-- name    : Formalism.HermitianLattices.Final.cumulant_and_partition_function_estimates
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:14.862793+00:00
-- url     : https://prove2.me/theorems/6604e1c1-539a-457b-ab08-6562599b068b
-- title:
--   Final: cumulant and partition function estimates
-- statement:
--   The Final construction uses the cumulant and partition function estimates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/FinalB.lean#L63-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/FinalB.lean#L63-L87

import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Definitions.Def_Formalism_GL3MeanSquares_FinalB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Final

theorem Formalism.HermitianLattices.Final.cumulant_and_partition_function_estimates :
    Formalism.HermitianLattices.CumulantEstimateDefs.SW_hecke_charsums ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.VolumeDependsOnSumOfRecurrence ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormLowerBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormUpperBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.CumulantUpperBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.SinhBounds ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.EigenvalueSumBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.DecayExponentLowerBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.TailAlongRay ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.HilbertSchmidtHalfBound ∧
    Formalism.HermitianLattices.CumulantEstimateDefs.UnipotentRadicalCard := by sorry
