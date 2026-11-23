-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_dual_eq
-- name    : Formalism.DivisionValues.OperatorNormFrames.opNormAt_dual_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:20.56474+00:00
-- url     : https://prove2.me/theorems/74abc9d8-4460-4445-94aa-b23893ef1981
-- title:
--   Operator Norm Frames: op Norm At dual eq
-- statement:
--   The Operator Norm Frames construction uses the op Norm At dual eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L108-L116

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

theorem Formalism.DivisionValues.OperatorNormFrames.opNormAt_dual_eq {K : Type} [Field K] [NumberField K] [StarRing K] {a D : ℕ}
    (XM : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ v, IsUnit (XE v).det) (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K))
    (v : InfinitePlace K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) XM (Pi.basisFun K (Fin D)).dualBasis
              (Formalism.HN.dualFrame XE) v B =
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((XE v)ᵀ * pmat v B * XM v))‖ := by sorry
