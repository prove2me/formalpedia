-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_coeff_X_single
-- name    : Formalism.FG.FormalGroupCoefficients.coeff_X_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:18.301423+00:00
-- url     : https://prove2.me/theorems/ee9e5a96-fe15-41f2-8bad-0fe391a3fa40
-- title:
--   Formal Group Coefficients: coeff X single
-- statement:
--   The Formal Group Coefficients construction uses the coeff X single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L34-L41

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
variable {R : Type u} [CommRing R]

theorem Formalism.FG.FormalGroupCoefficients.coeff_X_single {σ : Type*} [DecidableEq σ] (i j : σ) :
    coeff (Finsupp.single i 1) (X j : MvPowerSeries σ R) = if i = j then 1 else 0 := by sorry
