-- Prove2me | Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_SF_mul_right
-- name    : Formalism.L2.SG.MeasureShiftInvariance.SF_mul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:59.476175+00:00
-- url     : https://prove2.me/theorems/4d9640ce-26a8-4e9c-b960-3903275b3315
-- title:
--   Measure Shift Invariance: SF mul right
-- statement:
--   The Measure Shift Invariance construction uses the SF mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L62-L66

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

theorem Formalism.L2.SG.MeasureShiftInvariance.SF_mul_right {S : Set G} {Ω : Set G} (h : SF S Ω) (y : G) : SF S {r | r * y ∈ Ω} := by sorry
