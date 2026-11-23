-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_ModEx_MG_range_toM
-- name    : CompanionTheory.D.Upq.ModEx.MG.range_toM
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:44.396121+00:00
-- url     : https://prove2.me/theorems/ec154619-56d4-4552-8716-f6bf58347870
-- title:
--   MG: range to M
-- statement:
--   The MG construction uses the range to M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L157-L161

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

theorem CompanionTheory.D.Upq.ModEx.MG.range_toM : Set.range (MG.toM : MG G hG → MtM m) = {x | Matrix.of x ∈ G} := by sorry
