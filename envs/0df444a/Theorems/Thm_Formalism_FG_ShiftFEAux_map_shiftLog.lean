-- Prove2me | Theorems.Thm_Formalism_FG_ShiftFEAux_map_shiftLog
-- name    : Formalism.FG.ShiftFEAux.map_shiftLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:08.449662+00:00
-- url     : https://prove2.me/theorems/1b0063ec-b8ba-4efe-b5da-0db2d1795dca
-- title:
--   Shift FEAux: map shift Log
-- statement:
--   The Shift FEAux construction uses the map shift Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L49-L54

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.FG
open Formalism.FG.ShiftFEAux
open MvPowerSeries
variable {K : Type*} [Field K] {l m : ℕ}

theorem Formalism.FG.ShiftFEAux.map_shiftLog (σ : K →+* K) (k : ZMod m) :
    map σ (shiftLog K l m k) = shiftLog K l m k := by sorry
