-- Prove2me | solution 1 for local_cartan_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:46.05874+00:00
-- url     : https://prove2.me/submissions/71d655db-3c51-48c2-8bf7-fec9d58d4166

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_HyperbolicPlane
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairDichotomy
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairSelection
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_StepGlue
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LocCartanPair
import Theorems.Thm_P2M_PI_SqPair_LCP_pair_split__894e7521d033
import Theorems.Thm_PI_SqPair_LCP_base_lagrangian
import Theorems.Thm_PI_SqPair_LCP_hyperbolic_plane
import Theorems.Thm_PI_SqPair_LCP_locCartanPair_of
import Theorems.Thm_PI_SqPair_LCP_pair_dichotomy
import Theorems.Thm_PI_SqPair_LCP_pair_selection
import Theorems.Thm_PI_SqPair_LCP_step_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SqPair.LocCartanPair :=
  PI.SqPair.LCP.locCartanPair_of PI.SqPair.LCP.pair_dichotomy PI.SqPair.LCP.base_lagrangian
    (PI.SqPair.LCP.step_of PI.SqPair.LCP.pair_selection PI.SqPair.LCP.hyperbolic_plane
      PI.SqPair.LCP.pair_split')
