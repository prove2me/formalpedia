-- Prove2me | solution 1 for g_lattice_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:26:33.760533+00:00
-- url     : https://prove2.me/submissions/73ea3e9c-c70a-4c84-a5f1-127e16fb6f9d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianGroupLattices_IsCMFormEOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DvGLatHerm
import Theorems.Thm_PI_Dv_GLatHermW_glatHerm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.Dv.GLatHerm := PI.Dv.GLatHermW.glatHerm
