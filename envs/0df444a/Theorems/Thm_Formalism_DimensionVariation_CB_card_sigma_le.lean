-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_CB_card_sigma_le
-- name    : Formalism.DimensionVariation.CB.card_sigma_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:10:29.347623+00:00
-- url     : https://prove2.me/theorems/9954fbe7-ee2b-4978-9e2d-4effcffec3af
-- title:
--   CB: card sigma le
-- statement:
--   The CB construction uses the card sigma le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L16-L22

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

theorem Formalism.DimensionVariation.CB.card_sigma_le {AA : Type} [Fintype AA] (Cl : AA → Type) [∀ a, Fintype (Cl a)] (h : ℝ)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) :
    (Fintype.card (Σ a, Cl a) : ℝ) ≤ (Fintype.card AA : ℝ) * h := by sorry
