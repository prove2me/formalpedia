-- Prove2me | Theorems.Thm_Formalism_FG_not_a_law_example
-- name    : Formalism.FG.not_a_law_example
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:02.518842+00:00
-- url     : https://prove2.me/theorems/007196c2-d61e-4ee1-89fb-ffae11609f14
-- title:
--   FG: not a law example
-- statement:
--   The FG construction uses the not a law example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/AdditiveLawExample.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/AdditiveLawExample.lean#L79-L85

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_AdditiveLawExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG
open MvPowerSeries Formalism.FG.FormalGroupSubstitution

theorem Formalism.FG.not_a_law_example : Formalism.FG.NotLawExample := by sorry
