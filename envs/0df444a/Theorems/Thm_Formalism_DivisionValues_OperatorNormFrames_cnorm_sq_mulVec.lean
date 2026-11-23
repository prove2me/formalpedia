-- Prove2me | Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_sq_mulVec
-- name    : Formalism.DivisionValues.OperatorNormFrames.cnorm_sq_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:16.126868+00:00
-- url     : https://prove2.me/theorems/fb2f7ac1-e1b6-41a6-9449-e7c21ebd4631
-- title:
--   Operator Norm Frames: cnorm sq mul Vec
-- statement:
--   The Operator Norm Frames construction uses the cnorm sq mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L272-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean#L272-L274

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

theorem Formalism.DivisionValues.OperatorNormFrames.cnorm_sq_mulVec {n d : ℕ} (Z : Matrix (Fin d) (Fin n) ℂ) (y : Fin n → ℂ) :
    ((Formalism.HermitianLatticesTheory.cnorm (Z.mulVec y) ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ (Zᴴ * Z).mulVec y := by sorry
