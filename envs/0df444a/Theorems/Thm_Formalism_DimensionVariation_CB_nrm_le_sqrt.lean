-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_CB_nrm_le_sqrt
-- name    : Formalism.DimensionVariation.CB.nrm_le_sqrt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:11:16.586505+00:00
-- url     : https://prove2.me/theorems/afe9a804-3c27-4cd3-92a4-ce7ccafa5c11
-- title:
--   CB: nrm le sqrt
-- statement:
--   The CB construction uses the nrm le sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L52-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L52-L78

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open Formalism.DimensionVariation.CB
open Formalism.DivisionValues.OperatorNormFrames

theorem Formalism.DimensionVariation.CB.nrm_le_sqrt {a b : ℕ} (X : Matrix (Fin a) (Fin a) ℂ) (X' : Matrix (Fin b) (Fin b) ℂ)
    (hX : IsUnit X.det) (M : Matrix (Fin b) (Fin a) ℂ) (Bd : ℝ) (hB : 0 ≤ Bd)
    (h : ∀ y, fnorm X' (M.mulVec y) ^ 2 ≤ Bd * fnorm X y ^ 2) :
    nrm (X'⁻¹ * M * X) ≤ Real.sqrt Bd := by sorry
