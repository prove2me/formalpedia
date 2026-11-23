-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_map_atYv
-- name    : Formalism.FG.HeightVAux.map_atYv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:18.666843+00:00
-- url     : https://prove2.me/theorems/f43dd23d-5e2e-49b1-a6a1-a676a3a91455
-- title:
--   Height VAux: map at Yv
-- statement:
--   The Height VAux construction uses the map at Yv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L104-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L104-L110

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

theorem Formalism.FG.HeightVAux.map_atYv {S : Type*} [CommRing S] (φ : R →+* S) (g : MvPowerSeries ι R) :
    map φ (atYv g) = atYv (map φ g) := by sorry
