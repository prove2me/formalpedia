-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_cbHyp_matrix
-- name    : Formalism.DimensionVariation.cbHyp_matrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:20:31.038856+00:00
-- url     : https://prove2.me/theorems/45f4d245-4add-4b95-98e6-3c2599a24bf0
-- title:
--   Dimension Variation: cb Hyp matrix
-- statement:
--   The Dimension Variation construction uses the cb Hyp matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L685-L704
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/PerEmbeddingCoupledBound.lean#L685-L704

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

theorem Formalism.DimensionVariation.cbHyp_matrix (K : Type) [Field K] [NumberField K] (m : ℕ) (c : Fin (m + 1) → ℕ)
    (Kj : ∀ j : Fin m, Matrix (Fin (c j.succ)) (Fin (c j.castSucc)) K)
    (tmax : Fin m → InfinitePlace K → ℝ) (h0 : ∀ j v, 0 ≤ tmax j v)
    (ht : ∀ j v q p, ‖v.embedding (Kj j q p)‖ ^ 2 ≤ tmax j v) :
    CBHyp (fun i _ => (1 : Matrix (Fin (c i)) (Fin (c i)) ℂ)) Kj (AA := fun i => Fin (c i))
      (fun _ _ => Unit) (fun _ _ => ℂ) (fun _ _ => 1) (fun _ _ x p => x p.1) (fun _ _ _ _ => 1)
      (fun j v p q => (v.embedding (Kj j q.1 p.1)) • ContinuousLinearMap.id ℂ ℂ) (fun _ => 1) tmax := by sorry
