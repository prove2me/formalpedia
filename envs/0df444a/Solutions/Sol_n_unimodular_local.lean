-- Prove2me | solution 1 for n_unimodular_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:34:52.956605+00:00
-- url     : https://prove2.me/submissions/138b8ca3-68bc-4773-bd9a-c5f738499472

import Definitions.Def_Formalism_PeriodIntegrals_NUnimodLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_FrameC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnimodularLattice_Transf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_NUnimodLoc
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_FC_frame_conjugation_unimodular
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_TR_transfer_holds
import Theorems.Thm_PI_NUnimodLoc_UnitaryGroupMassFormula_nUnimodLoc_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.NUnimodLoc.NUnimodLoc :=
  PI.NUnimodLoc.UnitaryGroupMassFormula.nUnimodLoc_of PI.NUnimodLoc.UnitaryGroupMassFormula.FC.frame_conjugation_unimodular
    PI.NUnimodLoc.UnitaryGroupMassFormula.TR.transfer_holds
