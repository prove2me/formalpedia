-- Prove2me | Theorems.Thm_Formalism_FG_ShiftFEAux_pow_inj
-- name    : Formalism.FG.ShiftFEAux.pow_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:32.871402+00:00
-- url     : https://prove2.me/theorems/2d224375-912b-449e-85ec-ed74f2927060
-- title:
--   Shift FEAux: pow inj
-- statement:
--   The Shift FEAux construction uses the pow inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L14-L15

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

theorem Formalism.FG.ShiftFEAux.pow_inj (hl : 2 ≤ l) {a b : ℕ} (h : (l ^ 2) ^ a = (l ^ 2) ^ b) : a = b := by sorry
