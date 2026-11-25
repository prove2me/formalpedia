-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_Quot_quotient_measure_trivial_subgroup
-- name    : CompanionTheory.D.Upq.Quot.quotient_measure_trivial_subgroup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:05.867246+00:00
-- url     : https://prove2.me/theorems/f0b50492-8efe-55e2-a36d-22f19874829e
-- title:
--   Quot: quotient measure trivial subgroup
-- statement:
--   The Quot construction uses the quotient measure trivial subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/ExistsQuotientMeasureUnitaryGroup.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/ExistsQuotientMeasureUnitaryGroup.lean#L46-L65

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

theorem CompanionTheory.D.Upq.Quot.quotient_measure_trivial_subgroup {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G)
    {μ : Measure (MtM m)} (hμ : IsHaarOnM G μ) (hr : IsRightInvM G μ) :
    QuotientSetting G {1} μ (dirac (oneM m)) μ := by sorry
