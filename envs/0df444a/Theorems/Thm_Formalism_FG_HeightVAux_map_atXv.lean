-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_map_atXv
-- name    : Formalism.FG.HeightVAux.map_atXv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:10.435291+00:00
-- url     : https://prove2.me/theorems/d49cc38b-3c11-41c5-9e55-b6967c600788
-- title:
--   Height VAux: map at Xv
-- statement:
--   The Height VAux construction uses the map at Xv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L96-L102

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
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [DecidableEq ι] {τ : Type*}

theorem Formalism.FG.HeightVAux.map_atXv {S : Type*} [CommRing S] (φ : R →+* S) (g : MvPowerSeries ι R) :
    map φ (atXv g) = atXv (map φ g) := by sorry
