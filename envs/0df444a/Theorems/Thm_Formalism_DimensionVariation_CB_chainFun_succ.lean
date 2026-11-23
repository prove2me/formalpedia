-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_CB_chainFun_succ
-- name    : Formalism.DimensionVariation.CB.chainFun_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:11:44.747803+00:00
-- url     : https://prove2.me/theorems/3ae82ccf-e089-4a4a-ba49-10481fdb98b7
-- title:
--   CB: chain Fun succ
-- statement:
--   The CB construction uses the chain Fun succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L589-L594
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L589-L594

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

theorem Formalism.DimensionVariation.CB.chainFun_succ {m : ℕ} {C : Fin (m + 2) → Type} (Kj : ∀ j : Fin (m + 1), C j.castSucc → C j.succ)
    (φ : C 0) (i : Fin (m + 1)) :
    chainFun Kj i.succ φ = chainFun (C := fun i => C i.succ) (fun j : Fin m => Kj j.succ) i (Kj 0 φ) := by sorry
