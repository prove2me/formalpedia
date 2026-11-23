-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_ModEx_rightInv_of_modD_one
-- name    : CompanionTheory.D.Upq.ModEx.rightInv_of_modD_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:46.718859+00:00
-- url     : https://prove2.me/theorems/dbb0e4a2-e610-4c4a-afac-85974822424c
-- title:
--   Mod Ex: right Inv of mod D one
-- statement:
--   The Mod Ex construction uses the right Inv of mod D one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L219-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L219-L241

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.ModEx
open PI PI.QuotSetU.UnitaryGroupMassFormula
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}

theorem CompanionTheory.D.Upq.ModEx.rightInv_of_modD_one (hG : IsMatGroup G) (h1 : ∀ g ∈ G, modD hG g = 1)
    (μ : Measure (MtM m)) (hμ : IsHaarOnM G μ) : IsRightInvM G μ := by sorry
