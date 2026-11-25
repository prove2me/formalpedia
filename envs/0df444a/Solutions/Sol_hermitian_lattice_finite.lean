-- Prove2me | solution 1 for hermitian_lattice_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:10:00.900679+00:00
-- url     : https://prove2.me/submissions/7ac10216-cf8a-42e7-a734-9cddb5ceede2

import Definitions.Def_Formalism_PeriodIntegrals_HermLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianLatticeFiniteness_HermLatFinMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HermLatFin
import Theorems.Thm_PI_HermLatFin_UnitaryGroupMassFormula_hermLatFin_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.HermLatFin.HermLatFin :=
  PI.HermLatFin.UnitaryGroupMassFormula.hermLatFin_main
