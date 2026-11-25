-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Quot_IsHaarOnM_lt_top_of_isCompact
-- name    : CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:30:24.015569+00:00
-- url     : https://prove2.me/theorems/9bcfaca1-6119-47c9-b800-fd8010b1ff42
-- title:
--   Is Haar On M: lt top of is Compact
-- statement:
--   The Is Haar On M construction uses the lt top of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean#L55-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean#L55-L67

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace Set
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Quot
open PI CompanionTheory.D.Upq.ModEx
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}

theorem CompanionTheory.D.Upq.Quot.IsHaarOnM.lt_top_of_isCompact (hG : IsMatGroup G) {μ : Measure (MtM m)}
    (hμ : IsHaarOnM G μ) {K : Set (MtM m)} (hK : IsCompact K) : μ K < ∞ := by sorry
