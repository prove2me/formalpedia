-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_CB_chainFun_sum
-- name    : Formalism.DimensionVariation.CB.chainFun_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:11:08.444961+00:00
-- url     : https://prove2.me/theorems/8ff55bb6-427c-43bf-a475-974fbf1f5357
-- title:
--   CB: chain Fun sum
-- statement:
--   The CB construction uses the chain Fun sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L596-L604
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L596-L604

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

theorem Formalism.DimensionVariation.CB.chainFun_sum {m : ℕ} {C : Fin (m + 1) → Type} [∀ i, AddCommMonoid (C i)]
    (Kj : ∀ j : Fin m, C j.castSucc →+ C j.succ) {X : Type} (s : Finset X) (x : X → C 0) (i : Fin (m + 1)) :
    chainFun (fun j => ⇑(Kj j)) i (∑ a ∈ s, x a) = ∑ a ∈ s, chainFun (fun j => ⇑(Kj j)) i (x a) := by sorry
