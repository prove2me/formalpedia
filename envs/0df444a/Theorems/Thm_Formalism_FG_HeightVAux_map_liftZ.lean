-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_map_liftZ
-- name    : Formalism.FG.HeightVAux.map_liftZ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:11.92286+00:00
-- url     : https://prove2.me/theorems/2a8ad483-cb8b-41e6-a94c-9706368560ee
-- title:
--   Height VAux: map lift Z
-- statement:
--   The Height VAux construction uses the map lift Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L136-L140

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

theorem Formalism.FG.HeightVAux.map_liftZ {σ : Type*} (g : MvPowerSeries σ ℚ_[l]) (hg : IntegralMv g) :
    map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (liftZ g hg) = g := by sorry
