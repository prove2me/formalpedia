-- Prove2me | Theorems.Thm_Formalism_G_is_comm_of_rat
-- name    : Formalism.G.is_comm_of_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:36.65071+00:00
-- url     : https://prove2.me/theorems/afc2c371-6633-4e03-b617-ddef2fef26a6
-- title:
--   G: is comm of rat
-- statement:
--   The G construction uses the is comm of rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L338-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L338-L358

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries

theorem Formalism.G.is_comm_of_rat : Formalism.G.IsCommOfRat := by sorry
