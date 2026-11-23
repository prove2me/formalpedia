-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_filter_last
-- name    : Formalism.DivisionValues.OperatorNormFrames.filter_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:51.484082+00:00
-- url     : https://prove2.me/theorems/1e539209-112f-4814-ba28-4a9219a165c2
-- title:
--   Operator Norm Frames: filter last
-- statement:
--   The Operator Norm Frames construction uses the filter last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L189-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L189-L193

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

theorem Formalism.DivisionValues.OperatorNormFrames.filter_last {m : ℕ} :
    Finset.univ.filter (fun i : Fin m => i.castSucc < Fin.last m) = Finset.univ := by sorry
