-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hsY
-- name    : Formalism.FG.FormalGroupCoefficients.hsY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:24.876805+00:00
-- url     : https://prove2.me/theorems/b4c1f51d-52cf-4e42-a2c3-67c3aa5f9db6
-- title:
--   Formal Group Coefficients: hs Y
-- statement:
--   The Formal Group Coefficients construction uses the hs Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L60-L61

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

theorem Formalism.FG.FormalGroupCoefficients.hsY : HasSubst (fun i : ι => (vY i : MvPowerSeries (Fin 2 × ι) R)) := by sorry
