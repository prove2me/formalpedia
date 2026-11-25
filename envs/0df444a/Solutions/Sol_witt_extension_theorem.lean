-- Prove2me | solution 1 for witt_extension_theorem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:40:34.351808+00:00
-- url     : https://prove2.me/submissions/323bcf61-d902-4d29-abfa-d0759516a363

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WittExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_OneVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_AnisotropicHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_WittOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Theorems.Thm_P2M_PI_Witt_anisotropic__ba4aff8f3cd5
import Theorems.Thm_PI_Witt_one_vector_holds
import Theorems.Thm_PI_Witt_witt_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.WittExtension :=
  PI.Witt.witt_of PI.Witt.one_vector_holds PI.Witt.anisotropic'
