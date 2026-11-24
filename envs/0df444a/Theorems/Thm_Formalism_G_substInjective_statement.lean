-- Prove2me | Theorems.Thm_Formalism_G_substInjective_statement
-- name    : Formalism.G.substInjective_statement
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:39.203409+00:00
-- url     : https://prove2.me/theorems/8cc649f5-436c-4d24-b379-b4aded1505e8
-- title:
--   G: subst Injective statement
-- statement:
--   The G construction uses the subst Injective statement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/HomPsSubstMvSubst.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/HomPsSubstMvSubst.lean#L165-L168

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.G

theorem Formalism.G.substInjective_statement : SubstInjective := by sorry
