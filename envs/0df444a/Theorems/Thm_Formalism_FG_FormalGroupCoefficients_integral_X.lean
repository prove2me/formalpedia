-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_integral_X
-- name    : Formalism.FG.FormalGroupCoefficients.integral_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:38:05.983715+00:00
-- url     : https://prove2.me/theorems/abf8cd62-2927-47e2-89d2-0c6ab9a1dade
-- title:
--   Formal Group Coefficients: integral X
-- statement:
--   The Formal Group Coefficients construction uses the integral X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L124-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L124-L127

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.FG.FormalGroupCoefficients.integral_X {τ : Type*} (x : τ) : IntegralMv (X x : MvPowerSeries τ K) := by sorry
