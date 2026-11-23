-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_ModEx_map_mul_right_of_modular_one
-- name    : CompanionTheory.D.Upq.ModEx.map_mul_right_of_modular_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:41.466831+00:00
-- url     : https://prove2.me/theorems/1af3f98a-0743-4bb8-8002-de04ce4c8822
-- title:
--   Mod Ex: map mul right of modular one
-- statement:
--   The Mod Ex construction uses the map mul right of modular one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L65-L73

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
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

theorem CompanionTheory.D.Upq.ModEx.map_mul_right_of_modular_one (h1 : ∀ g : H, modularCharacterFun g = 1)
    (ν : Measure H) [SigmaFinite ν] [IsMulLeftInvariant ν] (g : H) : map (· * g) ν = ν := by sorry
