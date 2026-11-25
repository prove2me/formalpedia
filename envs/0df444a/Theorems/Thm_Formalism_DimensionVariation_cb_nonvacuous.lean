-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_cb_nonvacuous
-- name    : Formalism.DimensionVariation.cb_nonvacuous
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:26:40.056707+00:00
-- url     : https://prove2.me/theorems/02ee1525-ea7a-4e3c-8590-955788566da9
-- title:
--   Dimension Variation: cb nonvacuous
-- statement:
--   The Dimension Variation construction uses the cb nonvacuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L706-L717
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L706-L717

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

theorem Formalism.DimensionVariation.cb_nonvacuous :
    CBHyp (K := ℚ) (m := 2) (c := fun _ => 2) (fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) (fun _ => 1)
      (AA := fun _ => Fin 2) (fun _ _ => Unit) (fun _ _ => ℂ) (fun _ _ => 1) (fun _ _ x p => x p.1)
      (fun _ _ _ _ => 1)
      (fun _ v p q => (v.embedding ((1 : Matrix (Fin 2) (Fin 2) ℚ) q.1 p.1)) • ContinuousLinearMap.id ℂ ℂ)
      (fun _ => 1) (fun _ _ => 1) ∧
    chainMat (R := ℚ) (m := 2) (c := fun _ => 2) (fun _ => 1) (Fin.last 2) ≠ 0 := by sorry
