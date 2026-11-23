-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_Poul_inner_map_left
-- name    : CompanionTheory.D.gk.Poul.inner_map_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:40.911029+00:00
-- url     : https://prove2.me/theorems/063de733-4d9e-4b09-ba99-117c63ca0b01
-- title:
--   Poul: inner map left
-- statement:
--   The Poul construction uses the inner map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsOpOfForm.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/HaarBumpFunctions/ExistsOpOfForm.lean#L14-L20

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_inner_map_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
variable {G : Type} [Group G] {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : G →* (H →L[ℂ] H)} {σ' : G →* (H' →L[ℂ] H')}
omit [CompleteSpace H]

theorem CompanionTheory.D.gk.Poul.inner_map_left (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (v w : H) : ⟪σ g v, w⟫_ℂ = ⟪v, σ g⁻¹ w⟫_ℂ := by sorry
