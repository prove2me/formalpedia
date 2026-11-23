-- Prove2me | Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_isFD_of_SF
-- name    : Formalism.L2.SG.MeasureShiftInvariance.isFD_of_SF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:57.871071+00:00
-- url     : https://prove2.me/theorems/94c1d0b7-5123-4341-a206-3c8dc67cb0e8
-- title:
--   Measure Shift Invariance: is FD of SF
-- statement:
--   The Measure Shift Invariance construction uses the is FD of SF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L17-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L17-L39

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

theorem Formalism.L2.SG.MeasureShiftInvariance.isFD_of_SF (Γ : Subgroup G) [Countable Γ] {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) (μ : Measure G) :
    IsFundamentalDomain Γ Ω μ := by sorry
