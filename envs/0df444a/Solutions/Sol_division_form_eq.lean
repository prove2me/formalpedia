-- Prove2me | solution 1 for division_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:01:10.179803+00:00
-- url     : https://prove2.me/submissions/9a4223e2-df1a-4022-82d0-6fed30f950bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceFormEquality_FormEqImage
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DvFormEq
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_form_eq_image
import Theorems.Thm_PI_Dv_HermitianFormEquivalence_form_one_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.Dv.SameFormAllLevels := by
  intro K _ σ G _ _ T P0 hM EE _ _ ρE M M' h
  have h1 : M.form 1 = M'.form 1 := by
    rw [PI.Dv.HermitianFormEquivalence.form_one_eq M P0 hM, PI.Dv.HermitianFormEquivalence.form_one_eq M' P0 hM, h]
  refine ⟨h1, fun P => ?_⟩
  rw [PI.Dv.HermitianFormEquivalence.form_eq_image M, PI.Dv.HermitianFormEquivalence.form_eq_image M', h1]
