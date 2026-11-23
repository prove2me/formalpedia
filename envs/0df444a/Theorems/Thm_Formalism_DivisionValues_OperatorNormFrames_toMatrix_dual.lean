-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_toMatrix_dual
-- name    : Formalism.DivisionValues.OperatorNormFrames.toMatrix_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:06.491852+00:00
-- url     : https://prove2.me/theorems/b1006fee-b0b2-4f73-94f2-0c91c9e016c2
-- title:
--   Operator Norm Frames: to Matrix dual
-- statement:
--   The Operator Norm Frames construction uses the to Matrix dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L96-L101

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.OperatorNormFrames

theorem Formalism.DivisionValues.OperatorNormFrames.toMatrix_dual {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) :
    (LinearMap.toMatrix (Pi.basisFun K (Fin a)) (Pi.basisFun K (Fin D)).dualBasis B).map v.embedding =
      pmat v B := by sorry
