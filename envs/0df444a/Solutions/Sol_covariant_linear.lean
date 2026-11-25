-- Prove2me | solution 1 for covariant_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:28.280808+00:00
-- url     : https://prove2.me/submissions/1ef65296-c513-44da-9dfd-0ce274e9c274

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantLinearProduct_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovLin
import Theorems.Thm_PI_QnCovLinW_qnCovLin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.QnCovLin :=
  PI.QnCovLinW.qnCovLin
