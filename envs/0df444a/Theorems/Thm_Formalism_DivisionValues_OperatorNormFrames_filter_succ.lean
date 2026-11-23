-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_filter_succ
-- name    : Formalism.DivisionValues.OperatorNormFrames.filter_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:33.205799+00:00
-- url     : https://prove2.me/theorems/c2745f57-8d53-4246-9d58-1767ff9a8282
-- title:
--   Operator Norm Frames: filter succ
-- statement:
--   The Operator Norm Frames construction uses the filter succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L176-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L176-L182

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

theorem Formalism.DivisionValues.OperatorNormFrames.filter_succ {m : ℕ} (j : Fin m) :
    Finset.univ.filter (fun i : Fin m => i.castSucc < j.succ) =
      insert j (Finset.univ.filter (fun i : Fin m => i.castSucc < j.castSucc)) := by sorry
