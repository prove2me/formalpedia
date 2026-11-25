-- Prove2me | solution 1 for squarefree_div_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:12:02.138958+00:00
-- url     : https://prove2.me/submissions/a33610ad-1956-4786-b233-e554e1bb17f1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqfDivDeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeDivisorDegree_CardMonicTwoRootsLe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SqfDivDeg
import Theorems.Thm_PI_SqfDivDeg_W_rootDense
import Theorems.Thm_PI_SqfDivDeg_W_sqfDivDeg_of_rootDense


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.SqfDivDeg.Claim :=
  PI.SqfDivDeg.W.sqfDivDeg_of_rootDense PI.SqfDivDeg.W.rootDense
