-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupSubstitution_atYv_X
-- name    : Formalism.FG.FormalGroupSubstitution.atYv_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:11.277888+00:00
-- url     : https://prove2.me/theorems/c702944d-66f1-4bf9-ad0a-a6772500e730
-- title:
--   Formal Group Substitution: at Yv X
-- statement:
--   The Formal Group Substitution construction uses the at Yv X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/AdditiveLawExample.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/AdditiveLawExample.lean#L25-L28

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
open Formalism Formalism.FG Formalism.FG.FormalGroupSubstitution
open MvPowerSeries

theorem Formalism.FG.FormalGroupSubstitution.atYv_X (j : Fin 2) :
    Formalism.FG.atYv (MvPowerSeries.X j : MvPowerSeries (Fin 2) ℤ) = Formalism.FG.vY j := by sorry
