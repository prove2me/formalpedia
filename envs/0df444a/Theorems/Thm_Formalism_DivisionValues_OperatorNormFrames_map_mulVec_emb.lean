-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_map_mulVec_emb
-- name    : Formalism.DivisionValues.OperatorNormFrames.map_mulVec_emb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:56.79548+00:00
-- url     : https://prove2.me/theorems/cf60589b-1413-4cfb-b4de-6d76817528c5
-- title:
--   Operator Norm Frames: map mul Vec emb
-- statement:
--   The Operator Norm Frames construction uses the map mul Vec emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L539-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L539-L544

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
variable {K : Type} [Field K] [NumberField K] {D : ℕ}

theorem Formalism.DivisionValues.OperatorNormFrames.map_mulVec_emb {n : ℕ} (v : InfinitePlace K) (N : Matrix (Fin D) (Fin n) K) (x : Fin n → K) :
    (fun i => v.embedding (N.mulVec x i)) = (N.map v.embedding).mulVec fun i => v.embedding (x i) := by sorry
