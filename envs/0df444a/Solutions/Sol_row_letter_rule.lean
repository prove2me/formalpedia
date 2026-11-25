-- Prove2me | solution 1 for row_letter_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:14:05.735398+00:00
-- url     : https://prove2.me/submissions/91ac2fbe-1b52-4223-a866-26793a4281ab

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RowLetter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_ChainRule
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowDerivationChainRule_NvFalseEq
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_RowLetter
import Theorems.Thm_PI_RL_W_chainRule
import Theorems.Thm_PI_RL_W_hdHom
import Theorems.Thm_PI_RL_W_keyCov
import Theorems.Thm_PI_RL_W_rowLetter_of
import Theorems.Thm_PI_RL_W_vecX


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.RowLetter :=
  PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom
