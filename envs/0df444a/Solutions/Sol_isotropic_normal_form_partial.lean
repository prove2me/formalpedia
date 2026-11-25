-- Prove2me | solution 1 for isotropic_normal_form_partial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:01:06.553598+00:00
-- url     : https://prove2.me/submissions/cba883f6-f1bc-4014-b914-a21b50aa401a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsotropicNormalFormPartial
import Theorems.Thm_NFOne_normFormOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.C3.IsotropicNormalFormPartial := NFOne.normFormOne
