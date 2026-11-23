-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_subst_shift_shiftLog
-- name    : Formalism.FG.HeightVAux.subst_shift_shiftLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:31.491222+00:00
-- url     : https://prove2.me/theorems/19f04ae0-26c6-445c-9b86-5559ddb4e6e7
-- title:
--   Height VAux: subst shift shift Log
-- statement:
--   The Height VAux construction uses the subst shift shift Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L17-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L17-L44

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.HeightVAux
open MvPowerSeries Formalism.G Formalism.LT
variable {K : Type*} [Field K] {l m : ℕ} [NeZero m]

theorem Formalism.FG.HeightVAux.subst_shift_shiftLog (hl : 2 ≤ l) (j : ZMod m) :
    subst (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) K)) (shiftLog K l m j) =
      shiftLog K l m (j - 1) := by sorry
