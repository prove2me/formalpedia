-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_prod_filter_succ
-- name    : Formalism.DivisionValues.OperatorNormFrames.prod_filter_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:55.384599+00:00
-- url     : https://prove2.me/theorems/2b1ccb0e-badf-4864-a81f-dac0c1030972
-- title:
--   Operator Norm Frames: prod filter succ
-- statement:
--   The Operator Norm Frames construction uses the prod filter succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L184-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L184-L187

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

theorem Formalism.DivisionValues.OperatorNormFrames.prod_filter_succ {m : ℕ} (k : Fin m → ℝ) (j : Fin m) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin m => i.castSucc < j.succ), k i =
      k j * ∏ i ∈ Finset.univ.filter (fun i : Fin m => i.castSucc < j.castSucc), k i := by sorry
