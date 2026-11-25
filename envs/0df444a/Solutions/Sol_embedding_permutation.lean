-- Prove2me | solution 1 for embedding_permutation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:07:41.473628+00:00
-- url     : https://prove2.me/submissions/18b199de-7131-4314-a054-f32257b5ba1f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_EmbPerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingPermutations_CjEq
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_EmbPerm
import Theorems.Thm_PI_EmbPermWork_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.EmbPerm := PI.EmbPermWork.main
