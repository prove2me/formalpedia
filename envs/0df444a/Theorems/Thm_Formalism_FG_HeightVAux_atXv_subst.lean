-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_atXv_subst
-- name    : Formalism.FG.HeightVAux.atXv_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:25.468125+00:00
-- url     : https://prove2.me/theorems/41d877b4-a28b-4206-b81c-05ebb69c13f9
-- title:
--   Height VAux: at Xv subst
-- statement:
--   The Height VAux construction uses the at Xv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L86-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L86-L89

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

theorem Formalism.FG.HeightVAux.atXv_subst (h : ι → MvPowerSeries ι R) (hh : ∀ i, constantCoeff (h i) = 0)
    (g : MvPowerSeries ι R) : atXv (subst h g) = subst (fun i => atXv (h i)) g := by sorry
