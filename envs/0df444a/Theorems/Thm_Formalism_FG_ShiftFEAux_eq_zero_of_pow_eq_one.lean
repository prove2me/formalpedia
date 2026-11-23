-- Prove2me | Theorems.Thm_Formalism_FG_ShiftFEAux_eq_zero_of_pow_eq_one
-- name    : Formalism.FG.ShiftFEAux.eq_zero_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:11.164803+00:00
-- url     : https://prove2.me/theorems/a57ccb3b-b16d-48d3-b944-e4893db3edb1
-- title:
--   Shift FEAux: eq zero of pow eq one
-- statement:
--   The Shift FEAux construction uses the eq zero of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L17-L18

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

theorem Formalism.FG.ShiftFEAux.eq_zero_of_pow_eq_one (hl : 2 ≤ l) {a : ℕ} (h : (l ^ 2) ^ a = 1) : a = 0 := by sorry
