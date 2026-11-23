-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_constantCoeff_atXv
-- name    : Formalism.FG.HeightVAux.constantCoeff_atXv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:37.733801+00:00
-- url     : https://prove2.me/theorems/ee47c25d-ab2c-49c5-b8aa-7649e77d7f54
-- title:
--   Height VAux: constant Coeff at Xv
-- statement:
--   The Height VAux construction uses the constant Coeff at Xv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L62-L64

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

theorem Formalism.FG.HeightVAux.constantCoeff_atXv {g : MvPowerSeries ι R} (hg : constantCoeff g = 0) :
    constantCoeff (atXv g) = 0 := by sorry
