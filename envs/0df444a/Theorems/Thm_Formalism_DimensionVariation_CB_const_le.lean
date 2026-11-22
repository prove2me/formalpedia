-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_CB_const_le
-- name    : Formalism.DimensionVariation.CB.const_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:20.592457+00:00
-- url     : https://prove2.me/theorems/13f02d13-5906-43e9-b663-cac050184d0f
-- title:
--   CB: const le
-- statement:
--   The CB construction uses the const le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L24-L37

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

theorem Formalism.DimensionVariation.CB.const_le {AA AA' : Type} [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (h h' t : ℝ) (ht : 0 ≤ t)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) (hh' : ∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') :
    ((Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ)) * t ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' t := by sorry
