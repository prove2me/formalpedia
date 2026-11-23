-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_dot_frames
-- name    : Formalism.DivisionValues.OperatorNormFrames.dot_frames
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:35.46808+00:00
-- url     : https://prove2.me/theorems/d9c712c8-a247-44e8-9129-7ed7df1f1601
-- title:
--   Operator Norm Frames: dot frames
-- statement:
--   The Operator Norm Frames construction uses the dot frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L103-L106

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

theorem Formalism.DivisionValues.OperatorNormFrames.dot_frames {a D : ℕ} (Y : Matrix (Fin D) (Fin D) ℂ) (M : Matrix (Fin D) (Fin a) ℂ)
    (X : Matrix (Fin a) (Fin a) ℂ) (x : Fin a → ℂ) (y : Fin D → ℂ) :
    y ⬝ᵥ (Yᵀ * M * X).mulVec x = (Y.mulVec y) ⬝ᵥ M.mulVec (X.mulVec x) := by sorry
