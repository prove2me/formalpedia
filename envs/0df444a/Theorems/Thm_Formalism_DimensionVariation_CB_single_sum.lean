-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_CB_single_sum
-- name    : Formalism.DimensionVariation.CB.single_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:11:57.155158+00:00
-- url     : https://prove2.me/theorems/5c1b3af1-4427-4dfd-8c02-00dba44f9086
-- title:
--   CB: single sum
-- statement:
--   The CB construction uses the single sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L606-L609
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L606-L609

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
open CB
open Formalism.DimensionVariation.CB

theorem Formalism.DimensionVariation.CB.single_sum {I X : Type} [DecidableEq I] {H : I → Type} [∀ i, AddCommMonoid (H i)] (i : I)
    (s : Finset X) (x : X → H i) :
    (Pi.single i (∑ a ∈ s, x a) : ∀ i, H i) = ∑ a ∈ s, Pi.single i (x a) := by sorry
