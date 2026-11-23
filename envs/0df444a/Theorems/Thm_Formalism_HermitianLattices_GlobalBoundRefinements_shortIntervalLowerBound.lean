-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GlobalBoundRefinements_shortIntervalLowerBound
-- name    : Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:43.092799+00:00
-- url     : https://prove2.me/theorems/54a1df16-7c18-48b2-978f-86b8d94514b7
-- title:
--   Global Bound Refinements: short Interval Lower Bound
-- statement:
--   The Global Bound Refinements construction uses the short Interval Lower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/GlobalBoundRefinements.lean#L222-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/GlobalBoundRefinements.lean#L222-L246

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_shortIntervalLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
open Formalism.HermitianLattices.GL2PrimeSums

theorem Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound : ShortIntervalLowerBound := by sorry
