-- Prove2me | Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_ind_inv_mul
-- name    : Formalism.L2.SG.MeasureShiftInvariance.ind_inv_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:16.176313+00:00
-- url     : https://prove2.me/theorems/8e9e275e-f424-47cf-be02-1fc26844b648
-- title:
--   Measure Shift Invariance: ind inv mul
-- statement:
--   The Measure Shift Invariance construction uses the ind inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L124-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L124-L129

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]

theorem Formalism.L2.SG.MeasureShiftInvariance.ind_inv_mul {M : Type*} [Zero M] [One M] {A : Set G} (y : G) :
    (fun r => A.indicator (1 : G → M) (r⁻¹ * y)) = {r | r⁻¹ * y ∈ A}.indicator 1 := by sorry
