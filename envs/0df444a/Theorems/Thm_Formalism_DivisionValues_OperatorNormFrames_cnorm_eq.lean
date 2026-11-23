-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_eq
-- name    : Formalism.DivisionValues.OperatorNormFrames.cnorm_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:38.933301+00:00
-- url     : https://prove2.me/theorems/2c3e753d-bd5e-41f9-8679-28afdabad901
-- title:
--   Operator Norm Frames: cnorm eq
-- statement:
--   The Operator Norm Frames construction uses the cnorm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L15-L18

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_cnorm_eq

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

theorem Formalism.DivisionValues.OperatorNormFrames.cnorm_eq {n : ℕ} (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n))‖ := by sorry
