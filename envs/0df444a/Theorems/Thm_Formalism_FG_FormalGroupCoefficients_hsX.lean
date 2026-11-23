-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hsX
-- name    : Formalism.FG.FormalGroupCoefficients.hsX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:14.942299+00:00
-- url     : https://prove2.me/theorems/b423a6d1-911f-4c9f-a68d-f9b946489ef8
-- title:
--   Formal Group Coefficients: hs X
-- statement:
--   The Formal Group Coefficients construction uses the hs X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L57-L58

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

theorem Formalism.FG.FormalGroupCoefficients.hsX : HasSubst (fun i : ι => (vX i : MvPowerSeries (Fin 2 × ι) R)) := by sorry
