-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupLawMap_coe_injective
-- name    : Formalism.FG.FormalGroupLawMap.coe_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:42.146193+00:00
-- url     : https://prove2.me/theorems/7c1460b1-6cc1-46d2-8be8-af869ac86903
-- title:
--   Formal Group Law Map: coe injective
-- statement:
--   The Formal Group Law Map construction uses the coe injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftAsm.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftAsm.lean#L28-L29

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Formalism.FG.FormalGroupLawMap.coe_injective (l : ℕ) [Fact l.Prime] : Function.Injective (PadicInt.Coe.ringHom (p := l)) := by sorry
