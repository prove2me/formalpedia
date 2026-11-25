-- Prove2me | solution 1 for exp_triangle_inequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:02:52.214041+00:00
-- url     : https://prove2.me/submissions/a93ace19-167c-457c-b903-281485d54fdd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ExpTriOfHorn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_NormDetConjExp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_ProdLeOfInjective
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ExpTri
import Theorems.Thm_PI_ET_expTri_of_horn
import Theorems.Thm_PI_ET_horn_of
import Theorems.Thm_PI_ET_kyFanDet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.ExpTri := PI.ET.expTri_of_horn (PI.ET.horn_of PI.ET.kyFanDet)
