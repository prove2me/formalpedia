-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_toZMod_eq_zero_iff
-- name    : Formalism.FG.HeightVAux.toZMod_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:15.200367+00:00
-- url     : https://prove2.me/theorems/01c52cce-95f6-47c4-a864-4c672b71efc1
-- title:
--   Height VAux: to ZMod eq zero iff
-- statement:
--   The Height VAux construction uses the to ZMod eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L147-L149

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
variable {l : ℕ} [Fact l.Prime]

theorem Formalism.FG.HeightVAux.toZMod_eq_zero_iff (x : ℤ_[l]) : PadicInt.toZMod x = 0 ↔ (l : ℤ_[l]) ∣ x := by sorry
