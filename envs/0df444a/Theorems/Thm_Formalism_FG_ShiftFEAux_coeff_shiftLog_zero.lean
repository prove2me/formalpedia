-- Prove2me | Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog_zero
-- name    : Formalism.FG.ShiftFEAux.coeff_shiftLog_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:31.984242+00:00
-- url     : https://prove2.me/theorems/e518ae21-8b0e-4fc1-809b-ca5110dabad9
-- title:
--   Shift FEAux: coeff shift Log zero
-- statement:
--   The Shift FEAux construction uses the coeff shift Log zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L43-L47

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

theorem Formalism.FG.ShiftFEAux.coeff_shiftLog_zero (j : ZMod m) (n : ZMod m →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) :
    coeff n (shiftLog K l m j) = 0 := by sorry
