-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_constantCoeff_of_map
-- name    : Formalism.FG.HeightVAux.constantCoeff_of_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:28.395479+00:00
-- url     : https://prove2.me/theorems/fa223037-455d-46b3-a0d1-fa72a8ce490f
-- title:
--   Height VAux: constant Coeff of map
-- statement:
--   The Height VAux construction uses the constant Coeff of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L127-L131

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

theorem Formalism.FG.HeightVAux.constantCoeff_of_map {σ : Type*} (x : MvPowerSeries σ ℤ_[l])
    (hx : constantCoeff (map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) x) = 0) :
    constantCoeff x = 0 := by sorry
