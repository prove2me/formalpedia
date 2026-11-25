-- Prove2me | solution 1 for traceSurjective_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:08:26.150386+00:00
-- url     : https://prove2.me/submissions/e245dc56-7759-48df-b4e8-bf2d59d09cf8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CMTraceOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMTraceSurjective_IsTrMulConjOfMem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CMTraceOnto
import Theorems.Thm_PI_CMT_coe_conj
import Theorems.Thm_PI_CMT_isTr_mul_fixed
import Theorems.Thm_PI_CMT_isTr_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.CMTraceOnto := by
  intro K _ _ _ hK a ha

  have hfix : PI.CMT.conj a = a := by
    apply NumberField.RingOfIntegers.ext
    rw [PI.CMT.coe_conj, ha]
  obtain ⟨x, hx⟩ := PI.CMT.isTr_mul_fixed hfix (PI.CMT.isTr_one hK.2.2)
  refine ⟨x, PI.CMT.conj x, PI.CMT.coe_conj x, ?_⟩
  rw [hx, mul_one]
