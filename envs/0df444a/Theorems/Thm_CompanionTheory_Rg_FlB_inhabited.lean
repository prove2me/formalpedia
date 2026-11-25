-- Prove2me | Theorems.Thm_CompanionTheory_Rg_FlB_inhabited
-- name    : CompanionTheory.Rg.FlB.inhabited
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:18:13.119028+00:00
-- url     : https://prove2.me/theorems/6a9e164f-72a4-4d70-9c0a-6168c0f0f92e
-- title:
--   Fl B: inhabited
-- statement:
--   The Fl B construction uses the inhabited property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/StSandwich.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/StSandwich.lean#L108-L112

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.Rg CompanionTheory.Rg.FlB

theorem CompanionTheory.Rg.FlB.inhabited (L : Type) [NontriviallyNormedField L] (n : ℕ) [IsUltrametricDist L] :
    ∃ Λ : AddSubgroup (Fin n → L), IsLat L Λ ∧ IsCong Λ (0 : L) (1 : (Fin n → L) ≃ₗ[L] (Fin n → L)) := by sorry
