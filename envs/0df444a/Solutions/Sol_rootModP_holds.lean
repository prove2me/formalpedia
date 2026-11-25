-- Prove2me | solution 1 for rootModP_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:09:29.822939+00:00
-- url     : https://prove2.me/submissions/570432eb-e696-4405-83ce-1985300be596

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArtinSchreierRoots_ExistsRootOC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ASRoot
import Theorems.Thm_PI_ArtSch_RootWork_exists_root_OC


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ArtSch.RootModP := by
  intro l _ c b
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨z, hz⟩ := PI.ArtSch.RootWork.exists_root_OC l c' b'
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [← map_pow, ← map_mul, ← map_sub, ← map_sub, hz, map_zero]
