-- Prove2me | solution 1 for hilbert_schmidt_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:14:43.451939+00:00
-- url     : https://prove2.me/submissions/24474b58-cfb6-450a-8cee-2d3c544e43b0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_HSBlocksMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_NormHSBlocks
import Theorems.Thm_NormHilbertSchmidtBlocks_hSBlocks_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.L2.SG.NormCut.HSBlocks :=
  NormHilbertSchmidtBlocks.hSBlocks_main
