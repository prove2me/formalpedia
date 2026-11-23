-- Prove2me | Theorems.Thm_Formalism_FG_HeightVAux_subst_atYv
-- name    : Formalism.FG.HeightVAux.subst_atYv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:18.59805+00:00
-- url     : https://prove2.me/theorems/2081049b-5a55-423b-946d-af78cc89c441
-- title:
--   Height VAux: subst at Yv
-- statement:
--   The Height VAux construction uses the subst at Yv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/HeightV.lean#L78-L84

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

theorem Formalism.FG.HeightVAux.subst_atYv (G : Fin 2 × ι → MvPowerSeries τ R) (hG : HasSubst G)
    (g : MvPowerSeries ι R) : subst G (atYv g) = subst (fun i => G (1, i)) g := by sorry
