-- Prove2me | solution 1 for unitary_unimodular_right_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:10:45.11832+00:00
-- url     : https://prove2.me/submissions/325cefad-bea6-4b17-98b0-d2aacb34931a

import Definitions.Def_Formalism_PeriodIntegrals_UJUnimod
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UJUnimod
import Theorems.Thm_Formalism_REAL_indefinite_unitary_unimodular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UJUnimod.UJRightInv :=
  fun n ε => ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
