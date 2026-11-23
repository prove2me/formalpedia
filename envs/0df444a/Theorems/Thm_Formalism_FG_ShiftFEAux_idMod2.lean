-- Prove2me | Theorems.Thm_Formalism_FG_ShiftFEAux_idMod2
-- name    : Formalism.FG.ShiftFEAux.idMod2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:03.731941+00:00
-- url     : https://prove2.me/theorems/671d81f9-61c8-4a46-9aec-b383bd265bb7
-- title:
--   Shift FEAux: id Mod2
-- statement:
--   The Shift FEAux construction uses the id Mod2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L56-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L56-L78

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

theorem Formalism.FG.ShiftFEAux.idMod2 (hl : 2 ≤ l) : IsIdMod2 (shiftLog K l m) := by sorry
