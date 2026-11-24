-- Prove2me | Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_SF_conj
-- name    : Formalism.L2.SG.MeasureShiftInvariance.SF_conj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:56.720805+00:00
-- url     : https://prove2.me/theorems/1e2e66e7-b2ef-480e-96ca-3b116d04ab63
-- title:
--   Measure Shift Invariance: SF conj
-- statement:
--   The Measure Shift Invariance construction uses the SF conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L85-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L85-L99

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

theorem Formalism.L2.SG.MeasureShiftInvariance.SF_conj {Γ : Subgroup G} {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) :
    SF (conjSub h Γ : Set G) {r | h * r * h⁻¹ ∈ Ω} := by sorry
