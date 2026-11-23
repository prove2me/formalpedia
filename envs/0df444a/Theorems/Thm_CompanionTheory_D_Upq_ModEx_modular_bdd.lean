-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_ModEx_modular_bdd
-- name    : CompanionTheory.D.Upq.ModEx.modular_bdd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:50.449655+00:00
-- url     : https://prove2.me/theorems/dd0727e4-1883-4094-b059-3ebff8d11961
-- title:
--   Mod Ex: modular bdd
-- statement:
--   The Mod Ex construction uses the modular bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L40-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SecondCountableQuotients/ModExists.lean#L40-L63

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

theorem CompanionTheory.D.Upq.ModEx.modular_bdd {V : Set H} (hV : IsCompact V) :
    ∃ M : ℝ, ∀ v ∈ V, (modularCharacterFun v : ℝ) ≤ M := by sorry
