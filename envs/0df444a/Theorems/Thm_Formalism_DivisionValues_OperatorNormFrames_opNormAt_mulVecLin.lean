-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_opNormAt_mulVecLin
-- name    : Formalism.DivisionValues.OperatorNormFrames.opNormAt_mulVecLin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:41.803804+00:00
-- url     : https://prove2.me/theorems/5e28ba30-34d7-419b-82b3-b3fb9abe9ee8
-- title:
--   Operator Norm Frames: op Norm At mul Vec Lin
-- statement:
--   The Operator Norm Frames construction uses the op Norm At mul Vec Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L451-L459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L451-L459

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
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames

theorem Formalism.DivisionValues.OperatorNormFrames.opNormAt_mulVecLin {K : Type} [Field K] [NumberField K] [StarRing K] {a b : ℕ}
    (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ) (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
    (v : InfinitePlace K) (N : Matrix (Fin b) (Fin a) K) :
    Formalism.HN.opNormAt (Pi.basisFun K (Fin a)) X (Pi.basisFun K (Fin b)) X' v (Matrix.mulVecLin N) =
      nrm ((X' v)⁻¹ * N.map v.embedding * X v) := by sorry
