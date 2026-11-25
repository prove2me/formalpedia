-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Quot_exists_quotient_measure_unitary_group
-- name    : CompanionTheory.D.Upq.Quot.exists_quotient_measure_unitary_group
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:47.786501+00:00
-- url     : https://prove2.me/theorems/31893b68-a6a5-563f-b115-1cf197310916
-- title:
--   Quot: exists quotient measure unitary group
-- statement:
--   The Quot construction uses the exists quotient measure unitary group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/ExistsQuotientMeasureUnitaryGroup.lean#L67-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/ExistsQuotientMeasureUnitaryGroup.lean#L67-L74

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_QuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Quot
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula CompanionTheory.D.Upq.ModEx
variable {m : ℕ}

theorem CompanionTheory.D.Upq.Quot.exists_quotient_measure_unitary_group (k r : ℕ) : ∃ μ : Measure (MtM (2 * r + k + 1)),
    QuotientSetting (UH (Hpk k r)) (UH (Hpk k r)) μ μ (dirac (oneM _)) ∧
    QuotientSetting (UH (Hpk k r)) {1} μ (dirac (oneM _)) μ := by sorry
