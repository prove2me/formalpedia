-- Prove2me | Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_mem_conjSub
-- name    : Formalism.L2.SG.MeasureShiftInvariance.mem_conjSub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:09.097691+00:00
-- url     : https://prove2.me/theorems/e8cef38c-a630-450f-a6ab-050d827fe36c
-- title:
--   Measure Shift Invariance: mem conj Sub
-- statement:
--   The Measure Shift Invariance construction uses the mem conj Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L72-L79

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
variable (h : G)

theorem Formalism.L2.SG.MeasureShiftInvariance.mem_conjSub {Γ : Subgroup G} {s : G} : s ∈ conjSub h Γ ↔ h * s * h⁻¹ ∈ Γ := by sorry
