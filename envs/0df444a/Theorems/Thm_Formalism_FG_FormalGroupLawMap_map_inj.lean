-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupLawMap_map_inj
-- name    : Formalism.FG.FormalGroupLawMap.map_inj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:25:01.955873+00:00
-- url     : https://prove2.me/theorems/810a7570-794f-44db-bd70-18231e8a18c9
-- title:
--   Formal Group Law Map: map inj
-- statement:
--   The Formal Group Law Map construction uses the map inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftAsm.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftAsm.lean#L14-L19

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupLawMap
open MvPowerSeries
variable {R S : Type*} [CommRing R] [CommRing S]

theorem Formalism.FG.FormalGroupLawMap.map_inj {σ : Type*} (h : R →+* S) (hh : Function.Injective h) {f g : MvPowerSeries σ R}
    (e : map h f = map h g) : f = g := by sorry
