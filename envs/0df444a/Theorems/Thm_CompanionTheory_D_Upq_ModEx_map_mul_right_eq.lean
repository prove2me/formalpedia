-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_ModEx_map_mul_right_eq
-- name    : CompanionTheory.D.Upq.ModEx.map_mul_right_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:30:22.970251+00:00
-- url     : https://prove2.me/theorems/707b9040-230b-4b2e-a157-e5ab4e9c50c1
-- title:
--   Mod Ex: map mul right eq
-- statement:
--   The Mod Ex construction uses the map mul right eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L16-L19

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

theorem CompanionTheory.D.Upq.ModEx.map_mul_right_eq (μ : Measure H) [IsHaarMeasure μ] (g : H) :
    map (· * g) μ = modularCharacterFun g • μ := by sorry
