-- Prove2me | Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_fd_instances
-- name    : Formalism.L2.SG.MeasureShiftInvariance.fd_instances
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:59.021359+00:00
-- url     : https://prove2.me/theorems/b1ce94ae-6985-4283-b768-32f8fb164b2c
-- title:
--   Measure Shift Invariance: fd instances
-- statement:
--   The Measure Shift Invariance construction uses the fd instances property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L287-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L287-L288

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
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem Formalism.L2.SG.MeasureShiftInvariance.fd_instances (Γ : Subgroup G) (ν : Measure G) (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) :
    MeasurableSMul Γ G ∧ SMulInvariantMeasure Γ G ν := by sorry
