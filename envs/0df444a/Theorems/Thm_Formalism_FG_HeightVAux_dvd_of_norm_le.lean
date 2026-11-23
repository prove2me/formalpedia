-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_dvd_of_norm_le
-- name    : Formalism.FG.HeightVAux.dvd_of_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:32.615739+00:00
-- url     : https://prove2.me/theorems/a55d8be0-f1de-4671-a87f-a20cbd928cbe
-- title:
--   Height VAux: dvd of norm le
-- statement:
--   The Height VAux construction uses the dvd of norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L142-L145

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

theorem Formalism.FG.HeightVAux.dvd_of_norm_le {x : ℤ_[l]}
    (hx : ‖(PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) x‖ ≤ ‖((l : ℕ) : ℚ_[l])‖) :
    (l : ℤ_[l]) ∣ x := by sorry
