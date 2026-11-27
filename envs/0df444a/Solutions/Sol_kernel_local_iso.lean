-- Prove2me | solution 1 for kernel_local_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:35:38.920283+00:00
-- url     : https://prove2.me/submissions/c4022fbf-7b28-4a78-8ddc-5d0e15dfee46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_KerLocIsoOfNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOne
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerLocIso
import Theorems.Thm_PI_KLW_kerLocIso_of_normOne
import Theorems.Thm_PI_KLW_normOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.KerIso.LocIso := PI.KLW.kerLocIso_of_normOne PI.KLW.normOne
