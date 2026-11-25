-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_CB_extra_le
-- name    : Formalism.DimensionVariation.CB.extra_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:26:36.685004+00:00
-- url     : https://prove2.me/theorems/bfdcc2c3-86b6-4e4a-a6fa-4c79ce2d6a32
-- title:
--   CB: extra le
-- statement:
--   The CB construction uses the extra le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L213-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L213-L222

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

theorem Formalism.DimensionVariation.CB.extra_le (a b f m N L La logg C8 : ℝ) (ha : a ≤ f * N ^ 2 * logg) (hb : b ≤ f * N ^ 2 * logg)
    (hf : 0 ≤ f) (hm : 1 ≤ m) (hL : 0 ≤ L) (hLLa : L ≤ La) (hg : logg ≤ C8 * L) (p8 : 0 ≤ C8) :
    a + b ≤ 2 * C8 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) := by sorry
