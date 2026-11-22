-- Prove2me | Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog_single
-- name    : Formalism.FG.ShiftFEAux.coeff_shiftLog_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:10.571361+00:00
-- url     : https://prove2.me/theorems/33d8e8fc-48ff-4273-ab19-63be436f8650
-- title:
--   Shift FEAux: coeff shift Log single
-- statement:
--   The Shift FEAux construction uses the coeff shift Log single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L25-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L25-L41

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

theorem Formalism.FG.ShiftFEAux.coeff_shiftLog_single (hl : 2 ≤ l) (j : ZMod m) (e : ℕ) :
    coeff (Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) (shiftLog K l m j) =
      ((l : K) ^ e)⁻¹ := by sorry
