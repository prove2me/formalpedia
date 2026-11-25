-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_lin
-- name    : Formalism.FG.FormalGroupCoefficients.lin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:24:46.238114+00:00
-- url     : https://prove2.me/theorems/7ca2da11-56c9-447c-a57e-5f1333424012
-- title:
--   Formal Group Coefficients: lin
-- statement:
--   The Formal Group Coefficients construction uses the lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L106-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L106-L116

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.FG Formalism.FG.FormalGroupCoefficients
open MvPowerSeries Formalism.G Formalism.LT
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {f : ι → MvPowerSeries ι R} {F : ι → MvPowerSeries (Fin 2 × ι) R}

theorem Formalism.FG.FormalGroupCoefficients.lin (hf : IsIdMod2 f) (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hFG : ∀ j, subst F (f j) = atXv (f j) + atYv (f j)) (i : ι) (x : Fin 2 × ι) :
    coeff (Finsupp.single x 1) (F i) = if x.2 = i then 1 else 0 := by sorry
