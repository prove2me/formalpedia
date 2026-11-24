-- Prove2me | Theorems.Thm_Formalism_L2_SG_MeasureShiftInvariance_SF_measure_univ
-- name    : Formalism.L2.SG.MeasureShiftInvariance.SF_measure_univ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:04.877115+00:00
-- url     : https://prove2.me/theorems/f9b4a93d-a114-437c-aef5-ceec404bd7c5
-- title:
--   Measure Shift Invariance: SF measure univ
-- statement:
--   The Measure Shift Invariance construction uses the SF measure univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L290-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean#L290-L297

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

theorem Formalism.L2.SG.MeasureShiftInvariance.SF_measure_univ (Γ : Subgroup G) [Countable Γ] (ν : Measure G)
    (hν : ∀ s ∈ Γ, ν.map (fun x => s * x) = ν) {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) :
    ν Set.univ = ∑' _g : Γ, ν Ω := by sorry
